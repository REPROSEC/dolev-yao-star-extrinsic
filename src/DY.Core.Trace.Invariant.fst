module DY.Core.Trace.Invariant

open DY.Core.Trace.Type
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Label

noeq
type state_predicate (cinvs:crypto_invariants) = {
  pred: trace -> principal -> nat -> bytes -> prop;
  // TODO: Do we want the later lemma?
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id content)
  ;
  pred_knowable:
    tr:trace ->
    prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures
      is_knowable_by cinvs (principal_state_label prin sess_id) tr content
    )
  ;
}

noeq
type trace_invariants (cinvs:crypto_invariants) = {
  state_pred: state_predicate cinvs;
  event_pred: trace -> principal -> string -> bytes -> prop;
}

noeq
type protocol_invariants = {
  crypto_invs: crypto_invariants;
  trace_invs: trace_invariants crypto_invs;
}

val trace_invariant: protocol_invariants -> trace -> prop
let rec trace_invariant invs tr =
  match tr with
  | Nil -> True
  | Snoc tr_init event ->
    trace_invariant invs tr_init /\ (
      match event with
      | MsgSent msg ->
        is_publishable invs.crypto_invs tr msg
      | SetState prin sess_id content -> (
        invs.trace_invs.state_pred.pred tr_init prin sess_id content
      )
      | Event prin tag content -> (
        invs.trace_invs.event_pred tr_init prin tag content
      )
      | _ -> True
    )

// TODO: the next lemmas have similar proofs
// maybe refactor?

// Lemma for attacker theorem
val msg_sent_on_network_are_publishable:
  invs:protocol_invariants -> tr:trace -> msg:bytes ->
  Lemma
  (requires
    trace_invariant invs tr /\
    msg_sent_on_network tr msg
  )
  (ensures is_publishable invs.crypto_invs tr msg)
let rec msg_sent_on_network_are_publishable invs tr msg =
  match tr with
  | Nil -> assert(False)
  | Snoc tr_init (MsgSent msg') -> (
    assert(tr_init <$ tr);
    if msg = msg' then ()
    else (
      msg_sent_on_network_are_publishable invs tr_init msg
    )
  )
  | Snoc tr_init _ ->
    assert(tr_init <$ tr);
    msg_sent_on_network_are_publishable invs tr_init msg


val state_was_set_implies_pred:
  invs:protocol_invariants -> tr:trace ->
  prin:principal -> sess_id:nat -> content:bytes ->
  Lemma
  (requires
    trace_invariant invs tr /\
    state_was_set tr prin sess_id content
  )
  (ensures invs.trace_invs.state_pred.pred tr prin sess_id content)
  [SMTPat (state_was_set tr prin sess_id content);
   SMTPat (trace_invariant invs tr);
  ]
let rec state_was_set_implies_pred invs tr prin sess_id content =
  match tr with
  | Nil -> assert(False)
  | Snoc tr_init (SetState prin' sess_id' content') -> (
    assert(tr_init <$ tr);
    if prin = prin' && sess_id = sess_id' && content = content' then (
      invs.trace_invs.state_pred.pred_later tr_init tr prin sess_id content
    ) else (
      state_was_set_implies_pred invs tr_init prin sess_id content;
      invs.trace_invs.state_pred.pred_later tr_init tr prin sess_id content
    )
  )
  | Snoc tr_init _ ->
    assert(tr_init <$ tr);
    state_was_set_implies_pred invs tr_init prin sess_id content;
    invs.trace_invs.state_pred.pred_later tr_init tr prin sess_id content

// Lemma for attacker theorem
val state_is_knowable_by:
  invs:protocol_invariants -> tr:trace ->
  prin:principal -> sess_id:nat -> content:bytes ->
  Lemma
  (requires
    trace_invariant invs tr /\
    state_was_set tr prin sess_id content
  )
  (ensures is_knowable_by invs.crypto_invs (principal_state_label prin sess_id) tr content)
let state_is_knowable_by invs tr prin sess_id content =
  invs.trace_invs.state_pred.pred_knowable tr prin sess_id content

val event_triggered_at_implies_pred:
  invs:protocol_invariants -> tr:trace ->
  i:nat -> prin:principal -> tag:string -> content:bytes ->
  Lemma
  (requires
    event_triggered_at tr i prin tag content /\
    trace_invariant invs tr
  )
  (ensures invs.trace_invs.event_pred (prefix tr i) prin tag content)
  [SMTPat (event_triggered_at tr i prin tag content);
   SMTPat (trace_invariant invs tr);
  ]
let rec event_triggered_at_implies_pred invs tr i prin tag content =
  if i+1 = DY.Core.Trace.Type.length tr then ()
  else (
    let Snoc tr_init _ = tr in
    event_triggered_at_implies_pred invs tr_init i prin tag content
  )
