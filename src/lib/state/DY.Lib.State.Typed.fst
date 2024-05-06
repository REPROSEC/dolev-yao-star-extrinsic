module DY.Lib.State.Typed

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Tagged

noeq
type typed_session_pred {|crypto_invariants|} (a:Type) {|parseable_serializeable bytes a|} = {
  pred: trace -> principal -> nat -> a -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:nat -> content:a ->
    Lemma
    (requires pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id content)
  ;
  pred_knowable:
    tr:trace -> prin:principal -> sess_id:nat -> content:a ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures is_well_formed _ (is_knowable_by (principal_state_label prin sess_id) tr) content)
  ;
}

val typed_session_pred_to_session_pred:
  {|crypto_invariants|} ->
  #a:Type -> {|parseable_serializeable bytes a|} ->
  typed_session_pred a -> session_pred
let typed_session_pred_to_session_pred #cinvs #a #ps_a tspred =
  {
    pred = (fun tr prin sess_id content_bytes ->
      match parse a content_bytes with
      | None -> False
      | Some content -> tspred.pred tr prin sess_id content
    );
    pred_later = (fun tr1 tr2 prin sess_id content_bytes ->
      let Some content = parse a content_bytes in
      tspred.pred_later tr1 tr2 prin sess_id content
    );
    pred_knowable = (fun tr prin sess_id content_bytes ->
      let Some content = parse a content_bytes in
      tspred.pred_knowable tr prin sess_id content;
      serialize_parse_inv_lemma a content_bytes;
      serialize_wf_lemma a (is_knowable_by (principal_state_label prin sess_id) tr) content
    );
  }

val has_typed_session_pred:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  invs:protocol_invariants -> (string & typed_session_pred a) ->
  prop
let has_typed_session_pred #a #ps_a invs (tag, spred) =
  has_session_pred invs (tag, (typed_session_pred_to_session_pred spred))

[@@ "opaque_to_smt"]
val typed_state_was_set:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  trace -> string -> principal -> nat -> a ->
  prop
let typed_state_was_set #a #ps_a tr tag prin sess_id content =
  tagged_state_was_set tr tag prin sess_id (serialize _ content)

[@@ "opaque_to_smt"]
val set_typed_state:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  string -> principal -> nat -> a -> crypto unit
let set_typed_state tag prin sess_id content =
  set_tagged_state tag prin sess_id (serialize _ content)

[@@ "opaque_to_smt"]
val get_typed_state:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  string -> principal -> nat -> crypto (option a)
let get_typed_state #a tag prin sess_id =
  let*? content_bytes = get_tagged_state tag prin sess_id in
  match parse a content_bytes with
  | None -> return None
  | Some content -> return (Some content)

val set_typed_state_invariant:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  {|invs:protocol_invariants|} ->
  tag:string -> spred:typed_session_pred a ->
  prin:principal -> sess_id:nat -> content:a -> tr:trace ->
  Lemma
  (requires
    spred.pred tr prin sess_id content /\
    trace_invariant tr /\
    has_typed_session_pred invs (tag, spred)
  )
  (ensures (
    let ((), tr_out) = set_typed_state tag prin sess_id content tr in
    trace_invariant tr_out /\
    typed_state_was_set tr_out tag prin sess_id content
  ))
  [SMTPat (set_typed_state tag prin sess_id content tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_typed_session_pred invs (tag, spred))]
let set_typed_state_invariant #a #ps_a #invs tag spred prin sess_id content tr =
  reveal_opaque (`%set_typed_state) (set_typed_state #a);
  reveal_opaque (`%typed_state_was_set) (typed_state_was_set #a);
  parse_serialize_inv_lemma #bytes a content

val get_typed_state_invariant:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  {|invs:protocol_invariants|} ->
  tag:string -> spred:typed_session_pred a ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_typed_session_pred invs (tag, spred)
  )
  (ensures (
    let (opt_content, tr_out) = get_typed_state tag prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> (
        spred.pred tr prin sess_id content
      )
    )
  ))
  [SMTPat (get_typed_state #a tag prin sess_id tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_typed_session_pred invs (tag, spred))]
let get_typed_state_invariant #a #ps_a #invs tag spred prin sess_id tr =
  reveal_opaque (`%get_typed_state) (get_typed_state #a)

val typed_state_was_set_implies_pred:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  invs:protocol_invariants -> tr:trace ->
  tag:string -> spred:typed_session_pred a ->
  prin:principal -> sess_id:nat -> content:a ->
  Lemma
  (requires
    typed_state_was_set tr tag prin sess_id content /\
    trace_invariant tr /\
    has_typed_session_pred invs (tag, spred)
  )
  (ensures spred.pred tr prin sess_id content)
  [SMTPat (typed_state_was_set tr tag prin sess_id content);
   SMTPat (trace_invariant tr);
   SMTPat (has_typed_session_pred invs (tag, spred));
  ]
let typed_state_was_set_implies_pred #a #ps_a invs tr tag spred prin sess_id content =
  parse_serialize_inv_lemma #bytes a content;
  reveal_opaque (`%typed_state_was_set) (typed_state_was_set #a)
