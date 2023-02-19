module DY.Lib.State.Map

open Comparse
open DY.Core.Label
open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Trace.Invariant
open DY.Core.Trace.Manipulation
open DY.Core.Bytes
open DY.Core.Bytes.Type
open DY.Lib.Comparse.Glue
open DY.Lib.State.Typed

#set-options "--fuel 0 --ifuel 0"

(*** Map state & invariants ***)

noeq type map_types (bytes:Type0) {|bytes_like bytes|} = {
  key: eqtype;
  ps_key: parser_serializer bytes key;
  value: Type0;
  ps_value: parser_serializer bytes value;
}

noeq type map_predicate (mt:map_types bytes) = {
  pred: crypto_predicates -> trace -> principal -> nat -> mt.key -> mt.value -> prop;
  pred_later: cpreds:crypto_predicates -> tr1:trace -> tr2:trace -> prin:principal -> sess_id:nat -> key:mt.key -> value:mt.value -> Lemma
    (requires pred cpreds tr1 prin sess_id key value /\ tr1 <$ tr2)
    (ensures pred cpreds tr2 prin sess_id key value)
  ;
  pred_knowable: cpreds:crypto_predicates -> tr:trace -> prin:principal -> sess_id:nat -> key:mt.key -> value:mt.value -> Lemma
    (requires pred cpreds tr prin sess_id key value)
    (ensures is_well_formed_prefix mt.ps_key (is_knowable_by cpreds (principal_state_label prin sess_id) tr) key /\ is_well_formed_prefix mt.ps_value (is_knowable_by cpreds (principal_state_label prin sess_id) tr) value)
  ;
}

noeq type map_elem_ (bytes:Type0) {|bytes_like bytes|} (mt:map_types bytes) = {
  [@@@ with_parser #bytes mt.ps_key]
  key: mt.key;
  [@@@ with_parser #bytes mt.ps_value]
  value: mt.value;
}

%splice [ps_map_elem_] (gen_parser (`map_elem_))
%splice [ps_map_elem__is_well_formed] (gen_is_well_formed_lemma (`map_elem_))

type map_elem = map_elem_ bytes

noeq type map_ (bytes:Type0) {|bytes_like bytes|} (mt:map_types bytes) = {
  [@@@ with_parser #bytes (ps_list (ps_map_elem_ mt))]
  key_values: list (map_elem_ bytes mt)
}

%splice [ps_map_] (gen_parser (`map_))
%splice [ps_map__is_well_formed] (gen_is_well_formed_lemma (`map_))

type map = map_ bytes

instance parseable_serializeable_map_ (bytes:Type0) {|bytes_like bytes|} (mt:map_types bytes) : parseable_serializeable bytes (map_ bytes mt) = mk_parseable_serializeable (ps_map_ mt)

val map_elem_invariant: #mt:map_types bytes -> cpreds:crypto_predicates -> map_predicate mt -> trace -> principal -> nat -> map_elem mt -> prop
let map_elem_invariant #mt cpreds mpred tr prin sess_id x =
  mpred.pred cpreds tr prin sess_id x.key x.value

val map_invariant:
  #mt:map_types bytes -> cpreds:crypto_predicates ->
  map_predicate mt -> trace -> principal -> nat -> map mt ->
  prop
let map_invariant #mt cpreds mpred tr prin sess_id st =
  for_allP (map_elem_invariant cpreds mpred tr prin sess_id) st.key_values

val map_invariant_eq:
  #mt:map_types bytes -> cpreds:crypto_predicates ->
  mpred:map_predicate mt -> tr:trace -> prin:principal -> sess_id:nat -> st:map mt ->
  Lemma
  (map_invariant cpreds mpred tr prin sess_id st <==> (forall x. List.Tot.memP x st.key_values ==> map_elem_invariant cpreds mpred tr prin sess_id x))
let map_invariant_eq #mt cpreds mpred tr prin sess_id st =
  for_allP_eq (map_elem_invariant cpreds mpred tr prin sess_id) st.key_values

val map_session_invariant:
  #mt:map_types bytes ->
  mpred:map_predicate mt ->
  typed_session_pred (map mt)
let map_session_invariant #mt mpred = {
  pred = (fun cpreds tr prin sess_id content -> map_invariant cpreds mpred tr prin sess_id content);
  pred_later = (fun cpreds tr1 tr2 prin sess_id content ->
    map_invariant_eq cpreds mpred tr1 prin sess_id content;
    map_invariant_eq cpreds mpred tr2 prin sess_id content;
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mpred.pred_later cpreds tr1 tr2 prin sess_id))
  );
  pred_knowable = (fun cpreds tr prin sess_id content ->
    let pre = (is_knowable_by cpreds (principal_state_label prin sess_id) tr) in
    map_invariant_eq cpreds mpred tr prin sess_id content;
    for_allP_eq (is_well_formed_prefix (ps_map_elem_ mt) pre) content.key_values;
    introduce forall x. map_elem_invariant cpreds mpred tr prin sess_id x ==> is_well_formed_prefix (ps_map_elem_ mt) pre x
    with (
      introduce _ ==> _ with _. (
        mpred.pred_knowable cpreds tr prin sess_id x.key x.value
      )
    )
  );
}

val has_map_session_invariant: #mt:map_types bytes -> mpred:map_predicate mt -> string -> protocol_predicates -> prop
let has_map_session_invariant #mt mpred label pr =
  has_typed_session_pred pr label (map_session_invariant mpred)

(*** Map API ***)

val initialize_map:
  mt:map_types bytes -> label:string -> prin:principal ->
  crypto nat
let initialize_map mt label prin =
  let* sess_id = new_session_id prin in
  let session: map mt = { key_values = [] } in
  set_typed_state label prin sess_id session;*
  return sess_id

val add_key_value:
  mt:map_types bytes -> label:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key -> value:mt.value ->
  crypto (option unit)
let add_key_value mt label prin sess_id key value =
  let*? the_map = get_typed_state label prin sess_id in
  let new_elem = {key; value;} in
  set_typed_state label prin sess_id { key_values = new_elem::the_map.key_values };*
  return (Some ())

#push-options "--fuel 1 --ifuel 1"
val find_value_aux: #mt:map_types bytes -> key:mt.key -> l:list (map_elem mt) -> Pure (option mt.value)
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

val find_value:
  mt:map_types bytes -> label:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key ->
  crypto (option mt.value)
let find_value mt label prin sess_id key =
  let*? the_map = get_typed_state label prin sess_id in
  return (find_value_aux key the_map.key_values)

#push-options "--fuel 1"
val initialize_map_invariant:
  preds:protocol_predicates ->
  mt:map_types bytes -> mpred:map_predicate mt -> label:string ->
  prin:principal ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_map_session_invariant mpred label preds
  )
  (ensures (
    let (_, tr_out) = initialize_map mt label prin tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (initialize_map mt label prin tr);
   SMTPat (has_map_session_invariant mpred label preds);
   SMTPat (trace_invariant preds tr)
  ]
let initialize_map_invariant preds mt mpred label prin tr = ()
#pop-options

#push-options "--fuel 1"
val add_key_value_invariant:
  preds:protocol_predicates ->
  mt:map_types bytes -> mpred:map_predicate mt -> label:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key -> value:mt.value ->
  tr:trace ->
  Lemma
  (requires
    mpred.pred preds.crypto_preds tr prin sess_id key value /\
    trace_invariant preds tr /\
    has_map_session_invariant mpred label preds
  )
  (ensures (
    let (_, tr_out) = add_key_value mt label prin sess_id key value tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (add_key_value mt label prin sess_id key value tr);
   SMTPat (has_map_session_invariant mpred label preds);
   SMTPat (trace_invariant preds tr)
  ]
let add_key_value_invariant preds mt mpred label prin sess_id key value tr =
  let (opt_the_map, tr) = get_typed_state #(map mt) label prin sess_id tr in
  match opt_the_map with
  | None -> ()
  | Some the_map -> ()
#pop-options

val find_value_invariant:
  preds:protocol_predicates ->
  mt:map_types bytes -> mpred:map_predicate mt -> label:string ->
  prin:principal -> sess_id:nat ->
  key:mt.key ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_map_session_invariant mpred label preds
  )
  (ensures (
    let (opt_value, tr_out) = find_value mt label prin sess_id key tr in
    trace_invariant preds tr_out /\ (
      match opt_value with
      | None -> True
      | Some value -> (
        mpred.pred preds.crypto_preds tr prin sess_id key value
      )
    )
  ))
  [SMTPat (find_value mt label prin sess_id key tr);
   SMTPat (has_map_session_invariant mpred label preds);
   SMTPat (trace_invariant preds tr);
  ]
let find_value_invariant preds mt mpred label prin sess_id key tr =
  let (opt_the_map, tr) = get_typed_state #(map mt) label prin sess_id tr in
  match opt_the_map with
  | None -> ()
  | Some the_map -> (
    map_invariant_eq preds.crypto_preds mpred tr prin sess_id the_map;
    match find_value_aux key the_map.key_values with
    | None -> ()
    | Some value -> ()
  )
