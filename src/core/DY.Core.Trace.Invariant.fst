module DY.Core.Trace.Invariant

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Label

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

/// The parameters of the trace invariant.

noeq
type trace_invariants {|crypto_invariants|} = {
  state_pred: state_predicate;
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
    invs.trace_invs.state_pred.pred tr prin sess_id content
  )
  | Event prin tag content -> (
    // Triggered protocol events satisfy the custom event predicate
    invs.trace_invs.event_pred tr prin tag content
  )
  | RevealLabel prin time ->
    exists b. rand_generated_at tr time b
    // There exists some bytes generated at this timestamp

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
