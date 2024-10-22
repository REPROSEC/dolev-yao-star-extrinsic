module DY.Lib.State.Map

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Tagged
open DY.Lib.State.Typed

#set-options "--fuel 0 --ifuel 0"

/// This module defines a generic state for maps.
/// It will be used by DY.Lib.State.PKI or DY.Lib.State.PrivateKeys,
/// but can also be useful when specifying a protocol.

(*** Map state & invariants ***)

/// The parameters necessary to define the map functions.

class map_types (key_t:eqtype) (value_t:Type0) = {
  tag: string;
  ps_key_t: parser_serializer bytes key_t;
  ps_value_t: parser_serializer bytes value_t;
}

/// Type for the map predicate, which is used to define the state predicate.
/// The map predicate relates a key and its associated value.

noeq type map_predicate {|crypto_invariants|} (key_t:eqtype) (value_t:Type0) {|mt:map_types key_t value_t|} = {
  pred: trace -> principal -> state_id -> key_t -> value_t -> prop;
  pred_later: tr1:trace -> tr2:trace -> prin:principal -> sess_id:state_id -> key:key_t -> value:value_t -> Lemma
    (requires pred tr1 prin sess_id key value /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id key value)
  ;
  pred_knowable: tr:trace -> prin:principal -> sess_id:state_id -> key:key_t -> value:value_t -> Lemma
    (requires pred tr prin sess_id key value)
    (ensures
      is_well_formed_prefix mt.ps_key_t (is_knowable_by (principal_tag_state_label prin (tag #key_t #value_t) sess_id) tr) key /\
      is_well_formed_prefix mt.ps_value_t (is_knowable_by (principal_tag_state_label prin (tag #key_t #value_t) sess_id) tr) value
    )
  ;
}

[@@ with_bytes bytes]
noeq type map_elem (key_t:eqtype) (value_t:Type0) {|mt:map_types key_t value_t|} = {
  [@@@ with_parser #bytes mt.ps_key_t]
  key: key_t;
  [@@@ with_parser #bytes mt.ps_value_t]
  value: value_t;
}

%splice [ps_map_elem] (gen_parser (`map_elem))
%splice [ps_map_elem_is_well_formed] (gen_is_well_formed_lemma (`map_elem))

[@@ with_bytes bytes]
noeq type map (key_t:eqtype) (value_t:Type0) {|mt:map_types key_t value_t|} = {
  [@@@ with_parser #bytes (ps_list (ps_map_elem key_t value_t))]
  key_values: list (map_elem key_t value_t)
}

%splice [ps_map] (gen_parser (`map))
%splice [ps_map_is_well_formed] (gen_is_well_formed_lemma (`map))

instance parseable_serializeable_bytes_map (key_t:eqtype) (value_t:Type0) {|map_types key_t value_t|} : parseable_serializeable bytes (map key_t value_t) = mk_parseable_serializeable (ps_map key_t value_t)

instance local_state_map (key_t:eqtype) (value_t:Type0) {|mt:map_types key_t value_t|}: local_state (map key_t value_t) = {
  tag = mt.tag;
  format = (parseable_serializeable_bytes_map key_t value_t);
}

val map_elem_invariant:
  {|crypto_invariants|} ->
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  map_predicate key_t value_t ->
  trace -> principal -> state_id -> map_elem key_t value_t ->
  prop
let map_elem_invariant #cinvs #key_t #value_t #mt mpred tr prin sess_id x =
  mpred.pred tr prin sess_id x.key x.value

val map_invariant:
  {|crypto_invariants|} ->
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  map_predicate key_t value_t ->
  trace -> principal -> state_id -> map key_t value_t ->
  prop
let map_invariant #cinvs #key_t #value_t #mt mpred tr prin sess_id st =
  for_allP (map_elem_invariant mpred tr prin sess_id) st.key_values

val map_invariant_eq:
  {|crypto_invariants|} ->
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  mpred:map_predicate key_t value_t ->
  tr:trace -> prin:principal -> sess_id:state_id -> st:map key_t value_t ->
  Lemma
  (map_invariant mpred tr prin sess_id st <==> (forall x. List.Tot.memP x st.key_values ==> map_elem_invariant mpred tr prin sess_id x))
let map_invariant_eq #cinvs #key_t #value_t #mt mpred tr prin sess_id st =
  for_allP_eq (map_elem_invariant mpred tr prin sess_id) st.key_values

val map_session_invariant:
  {|crypto_invariants|} ->
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  mpred:map_predicate key_t value_t ->
  local_state_predicate (map key_t value_t)
let map_session_invariant #cinvs #key_t #value_t #mt mpred = {
  pred = (fun tr prin sess_id content -> map_invariant mpred tr prin sess_id content);
  pred_later = (fun tr1 tr2 prin sess_id content ->
    map_invariant_eq mpred tr1 prin sess_id content;
    map_invariant_eq mpred tr2 prin sess_id content;
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mpred.pred_later tr1 tr2 prin sess_id))
  );
  pred_knowable = (fun tr prin sess_id content ->
    let pre1 = (is_knowable_by (principal_tag_state_label prin (tag #key_t #value_t) sess_id) tr) in
    let pre2 = (is_knowable_by (principal_typed_state_content_label prin (tag #key_t #value_t) sess_id content) tr) in
    map_invariant_eq mpred tr prin sess_id content;
    for_allP_eq (is_well_formed_prefix (ps_map_elem key_t value_t) pre2) content.key_values;
    introduce forall x. map_elem_invariant mpred tr prin sess_id x ==> is_well_formed_prefix (ps_map_elem key_t value_t) pre2 x
    with (
      introduce _ ==> _ with _. (
        mpred.pred_knowable tr prin sess_id x.key x.value;
        is_well_formed_prefix_weaken (ps_map_elem key_t value_t) pre1 pre2 x
      )
    )
  );
}

val has_map_session_invariant:
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  {|protocol_invariants|} -> map_predicate key_t value_t -> prop
let has_map_session_invariant #key_t #value_t #mt #invs mpred =
  has_local_state_predicate (map_session_invariant mpred)

(*** Map API ***)

[@@ "opaque_to_smt"]
val initialize_map:
  key_t:eqtype -> value_t:Type0 ->
  {|map_types key_t value_t|} ->
  prin:principal ->
  traceful state_id
let initialize_map key_t value_t #mt prin =
  let* sess_id = new_session_id prin in
  let session: map key_t value_t = { key_values = [] } in
  set_state prin sess_id session;*
  return sess_id

[@@ "opaque_to_smt"]
val add_key_value:
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  prin:principal -> sess_id:state_id ->
  key:key_t -> value:value_t ->
  traceful (option unit)
let add_key_value #key_t #value_t #mt prin sess_id key value =
  let*? the_map = get_state prin sess_id in
  let new_elem = {key; value;} in
  set_state prin sess_id { key_values = new_elem::the_map.key_values };*
  return (Some ())

#push-options "--fuel 1 --ifuel 1"
val find_value_aux:
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  key:key_t -> l:list (map_elem key_t value_t) ->
  Pure (option value_t)
  (requires True)
  (ensures fun res ->
    match res with
    | None -> True
    | Some value -> List.Tot.memP ({key; value;}) l
  )
let rec find_value_aux #key_t #value_t #mt key l =
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
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  prin:principal -> sess_id:state_id ->
  key:key_t ->
  traceful (option value_t)
let find_value #key_t #value_t #mt prin sess_id key =
  let*? the_map = get_state prin sess_id in
  return (find_value_aux key the_map.key_values)

#push-options "--fuel 1"
val initialize_map_invariant:
  {|protocol_invariants|} ->
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  mpred:map_predicate key_t value_t ->
  prin:principal ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_map_session_invariant mpred
  )
  (ensures (
    let (_, tr_out) = initialize_map key_t value_t prin tr in
    trace_invariant tr_out
  ))
  [SMTPat (initialize_map key_t value_t prin tr);
   SMTPat (has_map_session_invariant mpred);
   SMTPat (trace_invariant tr)
  ]
let initialize_map_invariant #invs #key_t #value_t #mt mpred prin tr =
  reveal_opaque (`%initialize_map) (initialize_map)
#pop-options

#push-options "--fuel 1"
val add_key_value_invariant:
  {|protocol_invariants|} ->
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  mpred:map_predicate key_t value_t ->
  prin:principal -> sess_id:state_id ->
  key:key_t -> value:value_t ->
  tr:trace ->
  Lemma
  (requires
    mpred.pred tr prin sess_id key value /\
    trace_invariant tr /\
    has_map_session_invariant mpred
  )
  (ensures (
    let (_, tr_out) = add_key_value prin sess_id key value tr in
    trace_invariant tr_out
  ))
  [SMTPat (add_key_value prin sess_id key value tr);
   SMTPat (has_map_session_invariant mpred);
   SMTPat (trace_invariant tr)
  ]
let add_key_value_invariant #invs #key_t #value_t #mt mpred prin sess_id key value tr =
  reveal_opaque (`%add_key_value) (add_key_value #key_t #value_t)
#pop-options

val find_value_same_trace:
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  prin:principal -> sess_id:state_id ->
  key:key_t ->
  tr:trace ->
  Lemma
  (ensures (
    let (opt_value, tr_out) = find_value #_ #value_t prin sess_id key tr in
    tr_out == tr
    ))
  [SMTPat (find_value #key_t #value_t prin sess_id key tr)]
let find_value_same_trace #key_t #value_t #mt prin sess_id key tr =
  reveal_opaque (`%find_value) (find_value #key_t #value_t)

val find_value_invariant:
  {|protocol_invariants|} ->
  #key_t:eqtype -> #value_t:Type0 -> {|map_types key_t value_t|} ->
  mpred:map_predicate key_t value_t ->
  prin:principal -> sess_id:state_id ->
  key:key_t ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_map_session_invariant mpred
  )
  (ensures (
    let (opt_value, tr_out) = find_value prin sess_id key tr in
      match opt_value with
      | None -> True
      | Some value -> (
        mpred.pred tr prin sess_id key value
      )
  ))
  [SMTPat (find_value #key_t #value_t prin sess_id key tr);
   SMTPat (has_map_session_invariant mpred);
   SMTPat (trace_invariant tr);
  ]
let find_value_invariant #invs #key_t #value_t #mt mpred prin sess_id key tr =
  reveal_opaque (`%find_value) (find_value #key_t #value_t);
  let (opt_the_map, tr) = get_state prin sess_id tr in
  match opt_the_map with
  | None -> ()
  | Some the_map -> (
    map_invariant_eq mpred tr prin sess_id the_map;
    match find_value_aux key the_map.key_values with
    | None -> ()
    | Some value -> ()
  )
