module DY.Core.Trace.Invariant

open DY.Core.Trace.State.Aux
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
module L = DY.Core.Label
open DY.Core.Trace.Type

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
///
/// The state of a principal consists of three levels:
/// * the **full state** of a principal consists of several **sessions**,
///   which are identified by a state_id
/// * a session is a chronologically ordered collection of **states**
///
/// In the state predicate, we can define predicates on all state levels.
/// All predicates give conditions on when a new state can be added.
/// 
/// For example:
/// consider a state consisting of
/// (a nonce, a counter, a user_id).
/// We could define the following predicates
/// * the nonce must be knowable to the storing principal (this is a predicate on a single state `pred`)
/// * the counter must increase within a session (this is a session predicate `session_pred`)
/// * the user_id must be unique across different sessions (this is a predicate on the full state `full_state_pred`)

noeq
type state_predicate (cinvs:crypto_invariants) = {
  // the three predicates for adding a new state
  pred: trace -> principal -> state_id -> state_raw -> prop;
  session_pred: trace -> session_raw -> principal -> state_id -> state_raw -> prop; // the session argument is the current session on the trace
  full_state_pred: trace -> full_state_raw -> principal -> state_id -> state_raw -> prop; // the full_state argument is the current full state on the trace

  // for single states, we enforce that the stored content is knowable to the storing principal
  pred_knowable:
    tr:trace ->
    prin:principal -> sess_id:state_id -> content:state_raw ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures
      is_knowable_by #cinvs (L.principal_state_label prin sess_id) tr content
    )
  ;
  
  // the predicate for single states must stay true if the trace grows
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:state_id -> content:state_raw ->
    Lemma
    (requires tr1 <$ tr2 /\ pred tr1 prin sess_id content)
    (ensures pred tr2 prin sess_id content)
  ;
  // the session predicate must stay true, 
  // if the trace grows but the session stays the same
  session_pred_grows: 
    tr1:trace -> tr2:trace -> 
    sess:session_raw -> prin:principal -> sess_id:state_id -> content:state_raw ->
    Lemma
      (requires
        tr1 <$ tr2 /\ session_pred tr1 sess prin sess_id content
      )
      (ensures
        session_pred tr2 sess prin sess_id content
      )
}

/// the predicates on the three state levels are combined to a `global_state_pred`

// convenience functions lifting the session and full state predicates to `option`
// (no restriction for `None`)
val session_pred_: {|cinvs: crypto_invariants|} -> {|sp:state_predicate cinvs|} -> trace -> option session_raw -> principal -> state_id -> state_raw -> prop
let session_pred_ #cinvs #sp  tr session prin sid content =
  match session with
  | None -> True
  | Some sess -> sp.session_pred tr sess prin sid content

val full_state_pred_: {|cinvs: crypto_invariants|} -> {|sp:state_predicate cinvs|} -> trace -> option full_state_raw -> principal -> state_id -> state_raw -> prop
let full_state_pred_ #cinvs #sp tr full_state prin sid content =
  match full_state with
  | None -> True
  | Some full_st -> sp.full_state_pred tr full_st prin sid content

/// the global state pred reads the current session and full state from the trace
/// and uses those as arguments for the corresponding predicates

val global_state_pred_: {|cinvs: crypto_invariants|} -> {|sp: state_predicate cinvs |} -> trace -> principal -> state_id -> state_raw -> prop
let global_state_pred_ #cinvs #sp tr prin sid content =
  let session = get_session prin sid tr in
  let full_state = get_full_state prin tr in
    sp.pred tr prin sid content
  /\ session_pred_ tr session prin sid content
  /\ full_state_pred_ tr full_state prin sid content 


/// the session predicate remains true
/// if the trace grows
/// but there are no more state entries for the principal and the session

val session_pred_later_:
  {|cinvs: crypto_invariants |} -> {|sp:state_predicate cinvs |} ->
  tr1:trace -> tr2:trace  -> p:principal -> sid:state_id -> cont:state_raw ->
  Lemma
    (requires 
        tr1 <$ tr2 
      /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
      /\ sp.session_pred tr1 (get_session_aux p sid tr1) p sid cont
    )
    (ensures sp.session_pred tr2 (get_session_aux p sid tr2) p sid cont)
let session_pred_later_ #_ #sp tr1 tr2 p sid cont =
  get_session_aux_same p sid tr1 tr2;
  let session = get_session_aux p sid tr1 in
  sp.session_pred_grows tr1 tr2 session p sid cont

/// The parameters of the trace invariant.

noeq
type trace_invariants (cinvs:crypto_invariants) = {
  state_pred: state_predicate cinvs;
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
  trace_invs: trace_invariants crypto_invs;
}

// `trace_invariants` cannot be a typeclass that is inherited by `protocol_invariants`,
// hence we simulate inheritance like this.

let state_pred {|invs:protocol_invariants|} = invs.trace_invs.state_pred.pred
let session_pred {|invs:protocol_invariants|} = invs.trace_invs.state_pred.session_pred
let full_state_pred {|invs:protocol_invariants|} = invs.trace_invs.state_pred.full_state_pred
let state_pred_knowable {|invs:protocol_invariants|} = invs.trace_invs.state_pred.pred_knowable
let state_pred_later {|invs:protocol_invariants|} = invs.trace_invs.state_pred.pred_later
let session_pred_grows {|invs:protocol_invariants|} = invs.trace_invs.state_pred.session_pred_grows
let session_pred_opt {|invs:protocol_invariants|} = session_pred_ #_ #invs.trace_invs.state_pred
let full_state_pred_opt {|invs:protocol_invariants|} = full_state_pred_ #_ #invs.trace_invs.state_pred
let global_state_pred {|invs:protocol_invariants|} = global_state_pred_ #invs.crypto_invs #invs.trace_invs.state_pred
let session_pred_later {|invs:protocol_invariants|} = session_pred_later_ #invs.crypto_invs #invs.trace_invs.state_pred
let event_pred {|invs:protocol_invariants|} = invs.trace_invs.event_pred



(*** Trace invariant definition ***)

/// The invariant that must be satisfied by each event in the trace.

val trace_event_invariant: {|protocol_invariants|} -> trace -> trace_event -> prop
let trace_event_invariant #invs tr event =
  match event with
  | MsgSent msg ->
    // Messages sent on the network are publishable
    is_publishable tr msg
  | SetState prin sess_id content -> (
    // Stored states satisfy the custom state predicate
    global_state_pred tr prin sess_id content
    // invs.trace_invs.state_pred.pred tr prin sess_id content
  )
  | Event prin tag content -> (
    // Triggered protocol events satisfy the custom event predicate
    invs.trace_invs.event_pred tr prin tag content
  )
  // No restriction on other trace events (e.g. random generation or corruption)
  | _ -> True

/// The trace invariant ensures that
/// each trace event satisfy the invariant define above.

[@@ "opaque_to_smt"]
val trace_invariant: {|protocol_invariants|} -> trace -> prop
let rec trace_invariant #invs tr =
  match tr with
  | Nil -> True
  | Snoc tr_init event ->
    trace_event_invariant tr_init event /\
    trace_invariant tr_init



(*** Lemmas on the trace invariant ***)


/// rephrasing of `trace_invariant` using `prefix_before_event`

val prefix_before_event_invariant:
  {|invs: protocol_invariants|} ->
  ev:trace_event -> tr:trace{event_exists tr ev} ->
  Lemma 
    (requires trace_invariant tr)
    (ensures trace_event_invariant (prefix_before_event ev tr) ev /\ trace_invariant (prefix_before_event ev tr))
let rec prefix_before_event_invariant #invs the_ev tr = 
  match tr with
  | Nil -> ()
  | Snoc init ev -> 
         reveal_opaque (`%trace_invariant) (trace_invariant);
         norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
         if ev = the_ev
           then ()
           else prefix_before_event_invariant the_ev init

/// If there is an event in the trace satisfying the invariants,
/// then this event satisfy the trace event invariant.

val event_at_implies_trace_event_invariant:
  {|protocol_invariants|} ->
  tr:trace -> i:timestamp -> event:trace_event ->
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

/// The remaining theorems are special cases of the theorem above.

/// Messages sent on the network are publishable.
/// (This is a key lemma for attacker theorem.)

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

/// States stored satisfy the global state predicate.
// only for the prefix right before the `SetState` event
val state_was_set_implies_global_state_pred:
  {|invs: protocol_invariants|} ->
  p:principal -> sid:state_id -> content:state_raw -> tr:trace ->
  Lemma
    (requires 
      trace_invariant tr
      /\ state_was_set tr p sid content
    )
    (ensures
      global_state_pred (prefix_before_event (SetState p sid content) tr) p sid content
    )
    [SMTPat (state_was_set tr p sid content); 
     SMTPat (trace_invariant #invs tr);
    ]
let state_was_set_implies_global_state_pred p sid cont tr =
  prefix_before_event_invariant (SetState p sid cont) tr

/// States stored satisfy the custom state predicate.
// together with `pred_later` this even holds for the complete trace
// (as opposed to the prefix above)
val state_was_set_implies_pred:
  {|invs: protocol_invariants|} -> tr:trace ->
  prin:principal -> sess_id:state_id -> content:state_raw ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr prin sess_id content
  )
  (ensures state_pred tr prin sess_id content)
  [SMTPat (state_was_set tr prin sess_id content);
   SMTPat (trace_invariant #invs tr);
  ]
let state_was_set_implies_pred #invs tr prin sess_id content =
  eliminate exists i. event_at tr i (SetState prin sess_id content)
  returns invs.trace_invs.state_pred.pred tr prin sess_id content
  with _. (
    event_at_implies_trace_event_invariant tr i (SetState prin sess_id content);
    invs.trace_invs.state_pred.pred_later (prefix tr i) tr prin sess_id content
  )


/// States stored are knowable by the corresponding principal and state identifier.
// (This is a key lemma for attacker theorem.)

val state_is_knowable_by:
  {|protocol_invariants|} -> tr:trace ->
  prin:principal -> sess_id:state_id -> content:state_raw ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr prin sess_id content
  )
  (ensures is_knowable_by (L.principal_state_label prin sess_id) tr content)
let state_is_knowable_by #invs tr prin sess_id content =
  eliminate exists ts. event_at tr ts (SetState prin sess_id content)
  returns (is_knowable_by #invs.crypto_invs (L.principal_state_label prin sess_id) tr content)
  with _. (
    event_at_implies_trace_event_invariant tr ts (SetState prin sess_id content);
    invs.trace_invs.state_pred.pred_later (prefix tr ts) tr prin sess_id content;
    state_pred_knowable tr prin sess_id content
  )
  

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
  event_at_implies_trace_event_invariant tr i (Event prin tag content)
