module DY.Lib.State.Map

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Typed

#set-options "--fuel 0 --ifuel 0"

/// This module defines a generic state for maps.
/// It will be used by DY.Lib.State.PKI or DY.Lib.State.PrivateKeys,
/// but can also be useful when specifying a protocol.

(*** Map state & invariants ***)

/// The parameters necessary to define the map functions.

noeq type map_types = {
  key: eqtype;
  ps_key: parser_serializer bytes key;
  value: Type0;
  ps_value: parser_serializer bytes value;
}

/// Type for the map predicate, which is used to define the state predicate.
/// The map predicate relates a key and its associated value.

noeq type map_predicate {|crypto_invariants|} (mt:map_types) = {
  pred: trace -> principal -> nat -> mt.key -> mt.value -> prop;
  pred_later: tr1:trace -> tr2:trace -> prin:principal -> sess_id:nat -> key:mt.key -> value:mt.value -> Lemma
    (requires pred tr1 prin sess_id key value /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id key value)
  ;
  pred_knowable: tr:trace -> prin:principal -> sess_id:nat -> key:mt.key -> value:mt.value -> Lemma
    (requires pred tr prin sess_id key value)
    (ensures is_well_formed_prefix mt.ps_key (is_knowable_by (principal_state_label prin sess_id) tr) key /\ is_well_formed_prefix mt.ps_value (is_knowable_by (principal_state_label prin sess_id) tr) value)
  ;
}

[@@ with_bytes bytes]
noeq type map_elem (mt:map_types) = {
  [@@@ with_parser #bytes mt.ps_key]
  key: mt.key;
  [@@@ with_parser #bytes mt.ps_value]
  value: mt.value;
}

%splice [ps_map_elem] (gen_parser (`map_elem))
%splice [ps_map_elem_is_well_formed] (gen_is_well_formed_lemma (`map_elem))

[@@ with_bytes bytes]
noeq type map (mt:map_types) = {
  [@@@ with_parser #bytes (ps_list (ps_map_elem mt))]
  key_values: list (map_elem mt)
}

%splice [ps_map] (gen_parser (`map))
%splice [ps_map_is_well_formed] (gen_is_well_formed_lemma (`map))

instance parseable_serializeable_map (mt:map_types) : parseable_serializeable bytes (map mt) = mk_parseable_serializeable (ps_map mt)

val map_elem_invariant: {|crypto_invariants|} -> #mt:map_types -> map_predicate mt -> trace -> principal -> nat -> map_elem mt -> prop
let map_elem_invariant #cinvs #mt mpred tr prin sess_id x =
  mpred.pred tr prin sess_id x.key x.value

val map_invariant:
  {|crypto_invariants|} -> #mt:map_types ->
  map_predicate mt -> trace -> principal -> nat -> map mt ->
  prop
let map_invariant #cinvs #mt mpred tr prin sess_id st =
  for_allP (map_elem_invariant mpred tr prin sess_id) st.key_values

val map_invariant_eq:
  {|crypto_invariants|} -> #mt:map_types ->
  mpred:map_predicate mt -> tr:trace -> prin:principal -> sess_id:nat -> st:map mt ->
  Lemma
  (map_invariant mpred tr prin sess_id st <==> (forall x. List.Tot.memP x st.key_values ==> map_elem_invariant mpred tr prin sess_id x))
let map_invariant_eq #cinvs #mt mpred tr prin sess_id st =
  for_allP_eq (map_elem_invariant mpred tr prin sess_id) st.key_values

val map_session_invariant:
  {|crypto_invariants|} ->
  #mt:map_types ->
  mpred:map_predicate mt ->
  typed_session_pred (map mt)
let map_session_invariant #cinvs #mt mpred = {
  pred = (fun tr prin sess_id content -> map_invariant mpred tr prin sess_id content);
  pred_later = (fun tr1 tr2 prin sess_id content ->
    map_invariant_eq mpred tr1 prin sess_id content;
    map_invariant_eq mpred tr2 prin sess_id content;
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mpred.pred_later tr1 tr2 prin sess_id))
  );
  pred_knowable = (fun tr prin sess_id content ->
    let pre = (is_knowable_by (principal_state_label prin sess_id) tr) in
    map_invariant_eq mpred tr prin sess_id content;
    for_allP_eq (is_well_formed_prefix (ps_map_elem mt) pre) content.key_values;
    introduce forall x. map_elem_invariant mpred tr prin sess_id x ==> is_well_formed_prefix (ps_map_elem mt) pre x
    with (
      introduce _ ==> _ with _. (
        mpred.pred_knowable tr prin sess_id x.key x.value
      )
    )
  );
}

val has_map_session_invariant: #mt:map_types -> protocol_invariants -> (string & map_predicate mt) -> prop
let has_map_session_invariant #mt invs (tag, mpred) =
  has_typed_session_pred invs (tag, (map_session_invariant mpred))

(*** Map API ***)

[@@ "opaque_to_smt"]
val initialize_map:
  mt:map_types -> tag:string -> prin:principal ->
  crypto nat
let initialize_map mt tag prin =
  let* sess_id = new_session_id prin in
  let session: map mt = { key_values = [] } in
  set_typed_state tag prin sess_id session;*
  return sess_id

[@@ "opaque_to_smt"]
val add_key_value:
  mt:map_types -> tag:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key -> value:mt.value ->
  crypto (option unit)
let add_key_value mt tag prin sess_id key value =
  let*? the_map = get_typed_state tag prin sess_id in
  let new_elem = {key; value;} in
  set_typed_state tag prin sess_id { key_values = new_elem::the_map.key_values };*
  return (Some ())

#push-options "--fuel 1 --ifuel 1"
val find_value_aux: #mt:map_types -> key:mt.key -> l:list (map_elem mt) -> Pure (option mt.value)
  (requires True)
  (ensures fun res ->
    match res with
    | None -> True
    | Some value -> List.Tot.memP ({key; value;}) l
  )
let rec find_value_aux #mt key l =
  match l with
  | [] -> None
  | h::t ->
    if h.key = key then
      Some h.value
    else
      match find_value_aux key t with
      | Some res -> Some res
      | None -> None
#pop-options

[@@ "opaque_to_smt"]
val find_value:
  mt:map_types -> tag:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key ->
  crypto (option mt.value)
let find_value mt tag prin sess_id key =
  let*? the_map = get_typed_state tag prin sess_id in
  return (find_value_aux key the_map.key_values)

#push-options "--fuel 1"
val initialize_map_invariant:
  {|invs:protocol_invariants|} ->
  mt:map_types -> mpred:map_predicate mt -> tag:string ->
  prin:principal ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_map_session_invariant invs (tag, mpred)
  )
  (ensures (
    let (_, tr_out) = initialize_map mt tag prin tr in
    trace_invariant tr_out
  ))
  [SMTPat (initialize_map mt tag prin tr);
   SMTPat (has_map_session_invariant invs (tag, mpred));
   SMTPat (trace_invariant tr)
  ]
let initialize_map_invariant #invs mt mpred tag prin tr =
  reveal_opaque (`%initialize_map) (initialize_map)
#pop-options

#push-options "--fuel 1"
val add_key_value_invariant:
  {|invs:protocol_invariants|} ->
  mt:map_types -> mpred:map_predicate mt -> tag:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key -> value:mt.value ->
  tr:trace ->
  Lemma
  (requires
    mpred.pred tr prin sess_id key value /\
    trace_invariant tr /\
    has_map_session_invariant invs (tag, mpred)
  )
  (ensures (
    let (_, tr_out) = add_key_value mt tag prin sess_id key value tr in
    trace_invariant tr_out
  ))
  [SMTPat (add_key_value mt tag prin sess_id key value tr);
   SMTPat (has_map_session_invariant invs (tag, mpred));
   SMTPat (trace_invariant tr)
  ]
let add_key_value_invariant #invs mt mpred tag prin sess_id key value tr =
  reveal_opaque (`%add_key_value) (add_key_value);
  let (opt_the_map, tr) = get_typed_state #(map mt) tag prin sess_id tr in
  match opt_the_map with
  | None -> ()
  | Some the_map -> ()
#pop-options

val find_value_invariant:
  {|invs:protocol_invariants|} ->
  mt:map_types -> mpred:map_predicate mt -> tag:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_map_session_invariant invs (tag, mpred)
  )
  (ensures (
    let (opt_value, tr_out) = find_value mt tag prin sess_id key tr in
    tr_out == tr /\ (
      match opt_value with
      | None -> True
      | Some value -> (
        mpred.pred tr prin sess_id key value
      )
    )
  ))
  [SMTPat (find_value mt tag prin sess_id key tr);
   SMTPat (has_map_session_invariant invs (tag, mpred));
   SMTPat (trace_invariant tr);
  ]
let find_value_invariant #invs mt mpred tag prin sess_id key tr =
  reveal_opaque (`%find_value) (find_value);
  let (opt_the_map, tr) = get_typed_state #(map mt) tag prin sess_id tr in
  match opt_the_map with
  | None -> ()
  | Some the_map -> (
    map_invariant_eq mpred tr prin sess_id the_map;
    match find_value_aux key the_map.key_values with
    | None -> ()
    | Some value -> ()
  )
