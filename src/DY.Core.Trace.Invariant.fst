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
      is_knowable_by (principal_state_label prin sess_id) tr content
    )
  ;
}

noeq
type trace_invariants (cinvs:crypto_invariants) = {
  state_pred: state_predicate cinvs;
  event_pred: trace -> principal -> string -> bytes -> prop;
}

class protocol_invariants = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  crypto_invs: crypto_invariants;
  trace_invs: trace_invariants crypto_invs;
}

let state_pred {|invs:protocol_invariants|} = invs.trace_invs.state_pred.pred
let state_pred_later {|invs:protocol_invariants|} = invs.trace_invs.state_pred.pred_later
let state_pred_knowable {|invs:protocol_invariants|} = invs.trace_invs.state_pred.pred_knowable
let event_pred {|invs:protocol_invariants|} = invs.trace_invs.event_pred

val trace_event_invariant: {|protocol_invariants|} -> trace -> trace_event -> prop
let trace_event_invariant #invs tr event =
  match event with
  | MsgSent msg ->
    is_publishable tr msg
  | SetState prin sess_id content -> (
    invs.trace_invs.state_pred.pred tr prin sess_id content
  )
  | Event prin tag content -> (
    invs.trace_invs.event_pred tr prin tag content
  )
  | _ -> True

[@@ "opaque_to_smt"]
val trace_invariant: {|protocol_invariants|} -> trace -> prop
let rec trace_invariant #invs tr =
  match tr with
  | Nil -> True
  | Snoc tr_init event ->
    trace_event_invariant tr_init event /\
    trace_invariant tr_init

val event_at_implies_trace_event_invariant:
  {|protocol_invariants|} ->
  tr:trace -> i:nat -> event:trace_event ->
  Lemma
  (requires
    event_at tr i event /\
    trace_invariant tr
  )
  (ensures
    trace_event_invariant (prefix tr i) event
  )
let rec event_at_implies_trace_event_invariant #invs tr i event =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  if i+1 = DY.Core.Trace.Type.length tr then ()
  else (
    let Snoc tr_init _ = tr in
    event_at_implies_trace_event_invariant tr_init i event
  )

// TODO: the next lemmas have similar proofs
// maybe refactor?

// Lemma for attacker theorem
val msg_sent_on_network_are_publishable:
  {|protocol_invariants|} -> tr:trace -> msg:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    msg_sent_on_network tr msg
  )
  (ensures is_publishable tr msg)
let msg_sent_on_network_are_publishable #invs tr msg =
  eliminate exists i. event_at tr i (MsgSent msg)
  returns is_publishable tr msg
  with _. (
    event_at_implies_trace_event_invariant tr i (MsgSent msg)
  )

val state_was_set_implies_pred:
  {|protocol_invariants|} -> tr:trace ->
  prin:principal -> sess_id:nat -> content:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr prin sess_id content
  )
  (ensures state_pred tr prin sess_id content)
  [SMTPat (state_was_set tr prin sess_id content);
   SMTPat (trace_invariant tr);
  ]
let state_was_set_implies_pred #invs tr prin sess_id content =
  eliminate exists i. event_at tr i (SetState prin sess_id content)
  returns invs.trace_invs.state_pred.pred tr prin sess_id content
  with _. (
    event_at_implies_trace_event_invariant tr i (SetState prin sess_id content);
    invs.trace_invs.state_pred.pred_later (prefix tr i) tr prin sess_id content
  )

// Lemma for attacker theorem
val state_is_knowable_by:
  {|protocol_invariants|} -> tr:trace ->
  prin:principal -> sess_id:nat -> content:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr prin sess_id content
  )
  (ensures is_knowable_by (principal_state_label prin sess_id) tr content)
let state_is_knowable_by #invs tr prin sess_id content =
  state_pred_knowable tr prin sess_id content

val event_triggered_at_implies_pred:
  {|protocol_invariants|} -> tr:trace ->
  i:nat -> prin:principal -> tag:string -> content:bytes ->
  Lemma
  (requires
    event_triggered_at tr i prin tag content /\
    trace_invariant tr
  )
  (ensures event_pred (prefix tr i) prin tag content)
  [SMTPat (event_triggered_at tr i prin tag content);
   SMTPat (trace_invariant tr);
  ]
let event_triggered_at_implies_pred #invs tr i prin tag content =
  event_at_implies_trace_event_invariant tr i (Event prin tag content)
