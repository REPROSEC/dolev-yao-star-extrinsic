module DY.Core.Trace.Invariant

open DY.Core.Trace.Type
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Label

noeq
type trace_predicates (pr:protocol_preds) = {
  state_pred: trace -> principal -> nat -> bytes -> prop;
  state_pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires state_pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures state_pred tr2 prin sess_id content)
  ;
  state_pred_knowable:
    tr:trace ->
    prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires state_pred tr prin sess_id content)
    (ensures
      is_knowable_by pr (principal_state_label prin sess_id) tr content
    )
  ;

  event_pred: trace -> principal -> string -> bytes -> prop;
  event_pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> tag:string -> content:bytes ->
    Lemma
    (requires event_pred tr1 prin tag content /\ tr1 <$ tr2)
    (ensures event_pred tr2 prin tag content)
}

noeq
type protocol_predicates = {
  pr: protocol_preds;
  trace_preds: trace_predicates pr;
}

val trace_invariant: protocol_predicates -> trace -> prop
let rec trace_invariant preds tr =
  match tr with
  | Nil -> True
  | Snoc tr_init event ->
    trace_invariant preds tr_init /\ (
      match event with
      | MsgSent msg ->
        is_publishable preds.pr tr msg
      | SetState prin sess_id content -> (
        preds.trace_preds.state_pred tr_init prin sess_id content
      )
      | Event prin tag content -> (
        preds.trace_preds.event_pred tr_init prin tag content
      )
      | _ -> True
    )

// TODO: the next lemmas have similar proofs
// maybe refactor?

val msg_sent_on_network_are_publishable:
  preds:protocol_predicates -> tr:trace -> msg:bytes ->
  Lemma
  (requires
    trace_invariant preds tr /\
    msg_sent_on_network tr msg
  )
  (ensures is_publishable preds.pr tr msg)
let rec msg_sent_on_network_are_publishable preds tr msg =
  match tr with
  | Nil -> assert(False)
  | Snoc tr_init (MsgSent msg') -> (
    assert(tr_init <$ tr);
    if msg = msg' then ()
    else (
      msg_sent_on_network_are_publishable preds tr_init msg
    )
  )
  | Snoc tr_init _ ->
    assert(tr_init <$ tr);
    msg_sent_on_network_are_publishable preds tr_init msg

val state_is_knowable_by:
  preds:protocol_predicates -> tr:trace ->
  prin:principal -> sess_id:nat -> content:bytes ->
  Lemma
  (requires
    trace_invariant preds tr /\
    state_was_set tr prin sess_id content
  )
  (ensures is_knowable_by preds.pr (principal_state_label prin sess_id) tr content)
let rec state_is_knowable_by preds tr prin sess_id content =
  match tr with
  | Nil -> assert(False)
  | Snoc tr_init (SetState prin' sess_id' content') -> (
    assert(tr_init <$ tr);
    if prin = prin' && sess_id = sess_id' && content = content' then (
      preds.trace_preds.state_pred_knowable tr_init prin sess_id content
    ) else (
      state_is_knowable_by preds tr_init prin sess_id content
    )
  )
  | Snoc tr_init _ ->
    assert(tr_init <$ tr);
    state_is_knowable_by preds tr_init prin sess_id content

// TODO: Does this lemma fits here?
val event_triggered_implies_pred:
  preds:protocol_predicates -> tr:trace ->
  prin:principal -> tag:string -> content:bytes ->
  Lemma
  (requires
    event_triggered tr prin tag content /\
    trace_invariant preds tr
  )
  (ensures preds.trace_preds.event_pred tr prin tag content)
let rec event_triggered_implies_pred preds tr prin tag content =
  match tr with
  | Nil -> assert(False)
  | Snoc tr_init (Event prin' tag' content') -> (
    if prin = prin' && tag = tag' && content = content' then (
      preds.trace_preds.event_pred_later tr_init tr prin tag content
    ) else (
      event_triggered_implies_pred preds tr_init prin tag content;
      preds.trace_preds.event_pred_later tr_init tr prin tag content
    )
  )
  | Snoc tr_init _ ->
    event_triggered_implies_pred preds tr_init prin tag content;
    preds.trace_preds.event_pred_later tr_init tr prin tag content
