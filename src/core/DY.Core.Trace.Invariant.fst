module DY.Core.Trace.Invariant

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Label

#set-options "--fuel 1 --ifuel 1"

/// This module contains the definition of the trace invariant `trace_invariant`.
/// The trace invariant is at the heart of DY* methodology for protocol security proofs.
/// Indeed, security proofs in DY* proceed in two steps:
/// - first, we prove that all reachable traces satisfy the trace invariant,
/// - then, we prove that traces that satisfy the trace invariant
///   ensure some security guarantees.
///
/// Because each cryptographic protocol need a custom trace invariant to be proved secure,
/// the trace invariant can be customised with specific state or event predicates with `trace_invariants`.

(*** Trace invariant parameters ***)

/// The trace invariant is customised by the state predicate.
/// The state predicate must be proved each time a principal stores a state.
/// A crucial property of the state predicate is that
/// the content stored in the state of a principal must be knowable (from the perspective of labels)
/// to this principal (and state identifier).
/// This property will then be an essential ingredient of the attacker knowledge theorem
/// (see DY.Core.Attacker.Knowledge.attacker_only_knows_publishable_values),
/// to ensure that the every bytestring obtained by the attacker by corruption are publishable.

noeq
type state_predicate {|crypto_invariants|} = {
  pred: trace -> principal -> state_id -> bytes -> prop;
  // TODO: Do we want the later lemma?
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:state_id -> content:bytes ->
    Lemma
    (requires pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id content)
  ;
  pred_knowable:
    tr:trace ->
    prin:principal -> sess_id:state_id -> content:bytes ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures
      is_knowable_by (principal_state_content_label prin sess_id content) tr content
    )
  ;
}

/// The state update predicate can be used to constrain how a principal's state is allowed
/// to evolve over time, for instance, requiring that some fields of the state are constant
/// once set, or that a counter is monotonically increasing.
/// To update a state (i.e., write to a principal, state_id pair that already had a state
/// entry on the current trace), the state predicate needs to hold for the new state, but
/// also the update predicate must hold, relating the old and new states (at the trace/time
/// where the update is taking place).

noeq
type state_update_predicate {|crypto_invariants|} = {
  update_pred: trace -> principal -> state_id -> bytes -> bytes -> prop;
  // TODO Should this hold? It seems quite natural that if an update
  // from A to B was allowed, it remains allowed. This works because we
  // talk about both the start and end of the update, rather than saying
  // "it is allowed to update from [current value] to B".
  update_pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:state_id ->
    b1:bytes -> b2:bytes ->
    Lemma
    (requires
      update_pred tr1 prin sess_id b1 b2 /\
      tr1 <$ tr2
    )
    (ensures update_pred tr2 prin sess_id b1 b2)
  ;
  // Do we want transitivity?
  update_pred_trans:
    tr:trace ->
    prin:principal -> sess_id:state_id ->
    b1:bytes -> b2:bytes -> b3:bytes ->
    Lemma
    (requires
      update_pred tr prin sess_id b1 b2 /\
      update_pred tr prin sess_id b2 b3
    )
    (ensures update_pred tr prin sess_id b1 b3)
  ;
  // Reflexivity too?
}

// Transitivity:
// - Pred transitive for any given trace?
//   - Would also need a later pred saying that the update pred is stable.
//   - Do these two hold? Probably easier to use than a single mixed transitivity pred.
// - Pred transitive as in later pred above?
//

/// The parameters of the trace invariant.

noeq
type trace_invariants {|crypto_invariants|} = {
  state_pred: state_predicate;
  state_update_pred: state_update_predicate;
  event_pred: trace -> principal -> string -> bytes -> prop;
}

/// The protocol invariants parameters
/// gather the cryptographic invariant parameters (defined DY.Core.Bytes)
/// and trace invariant parameters (defined above).
/// These are all the invariant parameters
/// that are used to prove a specific protocol secure.

class protocol_invariants = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  crypto_invs: crypto_invariants;
  trace_invs: trace_invariants;
}

// `trace_invariants` cannot be a typeclass that is inherited by `protocol_invariants`,
// hence we simulate inheritance like this.

let state_pred {|invs:protocol_invariants|} = invs.trace_invs.state_pred
let state_update_pred {|invs:protocol_invariants|} = invs.trace_invs.state_update_pred
let event_pred {|invs:protocol_invariants|} = invs.trace_invs.event_pred

(*** Trace invariant definition ***)

/// The invariant that must be satisfied by each entry in the trace.

val trace_entry_invariant: {|protocol_invariants|} -> trace -> trace_entry -> prop
let trace_entry_invariant #invs tr entry =
  match entry with
  | MsgSent msg ->
    // Messages sent on the network are publishable
    is_publishable tr msg
  | SetState prin sess_id content -> (
    // Stored states satisfy the custom state predicate
    invs.trace_invs.state_pred.pred tr prin sess_id content /\
    (
      let is_state_for prin sess_id e =
        match e with
        | SetState prin' sess_id' content -> prin = prin' && sess_id = sess_id'
        | _ -> false
      in
      let ts_old_opt = trace_search_last tr (is_state_for prin sess_id) in
      match ts_old_opt with
      | None -> True
      | Some ts_old -> (
        let SetState _ _ content_old = get_entry_at tr ts_old in
        invs.trace_invs.state_update_pred.update_pred tr prin sess_id content_old content
      )
    )
  )
  | Event prin tag content -> (
    // Triggered protocol events satisfy the custom event predicate
    invs.trace_invs.event_pred tr prin tag content
  )
  // No restriction on other trace events (e.g. random generation or corruption)
  | _ -> True

/// The trace invariant ensures that
/// each trace entry satisfy the invariant define above.

[@@ "opaque_to_smt"]
val trace_invariant: {|protocol_invariants|} -> trace -> prop
let rec trace_invariant #invs tr =
  match tr with
  | Nil -> True
  | Snoc tr_init entry ->
    trace_entry_invariant tr_init entry /\
    trace_invariant tr_init

(*** Lemmas on the trace invariant ***)

/// If the trace invariant holds on a trace,
/// then it must hold on the trace's prefixes.

val trace_invariant_before:
  {|protocol_invariants|} ->
  tr1:trace -> tr2:trace ->
  Lemma
  (requires trace_invariant tr2 /\ tr1 <$ tr2)
  (ensures trace_invariant tr1)
  (decreases tr2)
let rec trace_invariant_before #invs tr1 tr2 =
  reveal_opaque (`%trace_invariant) (trace_invariant);
  reveal_opaque (`%prefix) (prefix #label);
  reveal_opaque (`%grows) (grows #label);
  if trace_length tr1 = trace_length tr2 then ()
  else (
    let Snoc init2 last2 = tr2 in
    trace_invariant_before tr1 init2
  )

/// If there is an entry in the trace satisfying the invariants,
/// then this entry satisfy the trace entry invariant.

val entry_at_implies_trace_entry_invariant:
  {|protocol_invariants|} ->
  tr:trace -> i:timestamp -> entry:trace_entry ->
  Lemma
  (requires
    entry_at tr i entry /\
    trace_invariant tr
  )
  (ensures
    trace_entry_invariant (prefix tr i) entry
  )
let rec entry_at_implies_trace_entry_invariant #invs tr i entry =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  if i+1 = trace_length tr then ()
  else (
    let Snoc tr_init _ = tr in
    entry_at_implies_trace_entry_invariant tr_init i entry
  )

/// The remaining theorems are special cases of the theorem above.

/// Messages sent on the network are publishable.
/// (This is a key lemma for attacker theorem.)

val msg_sent_on_network_are_publishable:
  {|protocol_invariants|} -> tr:trace -> msg:bytes ->
  Lemma
  (requires
    msg_sent_on_network tr msg /\
    trace_invariant tr
  )
  (ensures is_publishable tr msg)
let msg_sent_on_network_are_publishable #invs tr msg =
  eliminate exists i. entry_at tr i (MsgSent msg)
  returns is_publishable tr msg
  with _. (
    entry_at_implies_trace_entry_invariant tr i (MsgSent msg)
  )

/// States stored satisfy the custom state predicate.

val state_was_set_implies_pred:
  {|protocol_invariants|} -> tr:trace ->
  prin:principal -> sess_id:state_id -> content:bytes ->
  Lemma
  (requires
    state_was_set tr prin sess_id content /\
    trace_invariant tr
  )
  (ensures state_pred.pred tr prin sess_id content)
  [SMTPat (state_was_set tr prin sess_id content);
   SMTPat (trace_invariant tr);
  ]
let state_was_set_implies_pred #invs tr prin sess_id content =
  eliminate exists i. entry_at tr i (SetState prin sess_id content)
  returns invs.trace_invs.state_pred.pred tr prin sess_id content
  with _. (
    entry_at_implies_trace_entry_invariant tr i (SetState prin sess_id content);
    invs.trace_invs.state_pred.pred_later (prefix tr i) tr prin sess_id content
  )

/// States stored are knowable by the corresponding principal and state identifier.
// (This is a key lemma for attacker theorem.)

val state_is_knowable_by:
  {|protocol_invariants|} -> tr:trace ->
  prin:principal -> sess_id:state_id -> content:bytes ->
  Lemma
  (requires
    state_was_set tr prin sess_id content /\
    trace_invariant tr
  )
  (ensures is_knowable_by (principal_state_content_label prin sess_id content) tr content)
let state_is_knowable_by #invs tr prin sess_id content =
  state_pred.pred_knowable tr prin sess_id content

/// If a state was known to be set at two different times, its value at those times
/// must be related by the update predicate.

val state_was_set_twice_implies_update_pred:
  {|protocol_invariants|} -> tr:trace ->
  ts1:timestamp -> ts2:timestamp ->
  prin:principal -> sess_id:state_id ->
  content1:bytes -> content2:bytes ->
  Lemma
  (requires
    state_was_set_at tr ts1 prin sess_id content1 /\
    state_was_set_at tr ts2 prin sess_id content2 /\
    ts1 < ts2 /\
    trace_invariant tr
  )
  (ensures
    state_update_pred.update_pred tr prin sess_id content1 content2
  )
  [SMTPat (state_was_set_at tr ts1 prin sess_id content1);
   SMTPat (state_was_set_at tr ts2 prin sess_id content2);
   SMTPat (trace_invariant tr);
  ]
let rec state_was_set_twice_implies_update_pred tr ts1 ts2 prin sess_id content1 content2 =
  let is_state_for prin sess_id e =
    match e with
    | SetState prin' sess_id' content -> prin = prin' && sess_id = sess_id'
    | _ -> false
  in
  let Some ts' = trace_search_last (prefix tr ts2) (is_state_for prin sess_id) in
  let SetState _ _ content' = get_entry_at tr ts' in

  entry_at_implies_trace_entry_invariant tr ts2 (SetState prin sess_id content2);
  state_update_pred.update_pred_later (prefix tr ts2) tr prin sess_id content' content2;

  if ts1 < ts'
  then (
    state_was_set_twice_implies_update_pred tr ts1 ts' prin sess_id content1 content';
    state_update_pred.update_pred_trans tr prin sess_id content1 content' content2;
    ()
  )
  else ()

/// Triggered protocol events satisfy the event predicate.

val event_triggered_at_implies_pred:
  {|protocol_invariants|} -> tr:trace ->
  i:timestamp -> prin:principal -> tag:string -> content:bytes ->
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
  entry_at_implies_trace_entry_invariant tr i (Event prin tag content)
