module DY.Example.NSL.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total
open DY.Example.NSL.Protocol.Total.Proof
open DY.Example.NSL.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module proves invariant preservation
/// for all the functions in DY.Example.NSL.Protocol.Stateful.

(*** Trace invariants ***)

/// The (local) state predicate.

let state_predicate_nsl: local_state_predicate nsl_session = {
  pred = (fun tr prin sess_id st ->
    match st with
    | InitiatorSentMsg1 bob n_a -> (
      let alice = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
      event_triggered tr alice (Initiate1 alice bob n_a)
    )
    | ResponderSentMsg2 alice n_a n_b -> (
      let bob = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_b /\
      event_triggered tr bob (Respond1 alice bob n_a n_b)
    )
    | InitiatorSentMsg3 bob n_a n_b  -> (
      let alice = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_b /\
      event_triggered tr alice (Initiate2 alice bob n_a n_b)
    )
    | ResponderReceivedMsg3 alice n_a n_b -> (
      let bob = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_b /\
      event_triggered tr bob (Respond2 alice bob n_a n_b)
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}

/// The (local) event predicate.

let event_predicate_nsl: event_predicate nsl_event =
  fun tr prin e ->
    match e with
    | Initiate1 alice bob n_a -> (
      prin == alice /\
      is_secret (join (principal_label alice) (principal_label bob)) tr n_a /\
      0 < DY.Core.Trace.Type.length tr /\
      rand_generated_at tr (DY.Core.Trace.Type.length tr - 1) n_a
    )
    | Respond1 alice bob n_a n_b -> (
      prin == bob /\
      is_secret (join (principal_label alice) (principal_label bob)) tr n_b /\
      0 < DY.Core.Trace.Type.length tr /\
      rand_generated_at tr (DY.Core.Trace.Type.length tr - 1) n_b
    )
    | Initiate2 alice bob n_a n_b -> (
      prin == alice /\
      event_triggered tr alice (Initiate1 alice bob n_a) /\ (
        is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
        event_triggered tr bob (Respond1 alice bob n_a n_b)
      )
    )
    | Respond2 alice bob n_a n_b -> (
      prin == bob /\
      event_triggered tr bob (Respond1 alice bob n_a n_b) /\ (
        is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
        event_triggered tr alice (Initiate2 alice bob n_a n_b)
      )
    )

/// List of all local state predicates.

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (local_state_nsl_session.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_nsl);
]

/// List of all local event predicates.

let all_events = [
  (event_nsl_event.tag, compile_event_pred event_predicate_nsl)
]

/// Create the global trace invariants.

let trace_invariants_nsl: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_nsl: protocol_invariants = {
  crypto_invs = crypto_invariants_nsl;
  trace_invs = trace_invariants_nsl;
}

/// Lemmas that the global state predicate contains all the local ones

// Below, the `has_..._predicate` are called with the implicit argument `#protocol_invariants_nsl`.
// This argument could be omitted as it can be instantiated automatically by F*'s typeclass resolution algorithm.
// However we instantiate it explicitly here so that the meaning of `has_..._predicate` is easier to understand.

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate #protocol_invariants_nsl) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  mk_state_pred_correct #protocol_invariants_nsl all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate #protocol_invariants_nsl) all_sessions)

val protocol_invariants_nsl_has_pki_invariant: squash (has_pki_invariant #protocol_invariants_nsl)
let protocol_invariants_nsl_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_nsl_has_private_keys_invariant: squash (has_private_keys_invariant #protocol_invariants_nsl)
let protocol_invariants_nsl_has_private_keys_invariant = all_sessions_has_all_sessions ()

// As an example, below `#protocol_invariants_nsl` is omitted and instantiated using F*'s typeclass resolution algorithm
val protocol_invariants_nsl_has_nsl_session_invariant: squash (has_local_state_predicate state_predicate_nsl)
let protocol_invariants_nsl_has_nsl_session_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct #protocol_invariants_nsl all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events))

// As an example, below `#protocol_invariants_nsl` is omitted and instantiated using F*'s typeclass resolution algorithm
val protocol_invariants_nsl_has_nsl_event_invariant: squash (has_event_pred event_predicate_nsl)
let protocol_invariants_nsl_has_nsl_event_invariant = all_events_has_all_events ()

(*** Proofs ***)

val prepare_msg1_proof:
  tr:trace ->
  alice:principal -> bob:principal ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (sess_id, tr_out) = prepare_msg1 alice bob tr in
    trace_invariant tr_out
  ))
let prepare_msg1_proof tr alice bob =
  ()

val send_msg1_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg1 global_sess_id alice sess_id tr in
    trace_invariant tr_out
  ))
let send_msg1_proof tr global_sess_id alice sess_id =
  match get_state alice sess_id tr with
  | (Some (InitiatorSentMsg1 bob n_a), tr) -> (
    match get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob tr with
    | (None, tr) -> ()
    | (Some pk_b, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label alice) 32 tr in
      compute_message1_proof tr alice bob pk_b n_a nonce
    )
  )
  | _ -> ()

val prepare_msg2_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_sess_id, tr_out) = prepare_msg2 global_sess_id bob msg_id tr in
    trace_invariant tr_out
  ))
let prepare_msg2_proof tr global_sess_id bob msg_id =
  match recv_msg msg_id tr with
  | (None, tr) -> ()
  | (Some msg, tr) -> (
    match get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") tr with
    | (None, tr) -> ()
    | (Some sk_b, tr) -> (
      decode_message1_proof tr bob msg sk_b
    )
  )

val send_msg2_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg2 global_sess_id bob sess_id tr in
    trace_invariant tr_out
  ))
let send_msg2_proof tr global_sess_id bob sess_id =
  match get_state bob sess_id tr with
  | (Some (ResponderSentMsg2 alice n_a n_b), tr) -> (
    match get_public_key bob global_sess_id.pki (PkEnc "NSL.PublicKey") alice tr with
    | (None, tr) -> ()
    | (Some pk_a, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label bob) 32 tr in
      compute_message2_proof tr bob {n_a; alice;} pk_a n_b nonce
    )
  )
  | (_, tr) -> ()

val prepare_msg3_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> sess_id:state_id -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_sess_id, tr_out) = prepare_msg3 global_sess_id alice sess_id msg_id tr in
    trace_invariant tr_out
  ))
let prepare_msg3_proof tr global_sess_id alice sess_id msg_id =
  match recv_msg msg_id tr with
  | (None, tr) -> ()
  | (Some msg, tr) -> (
    match get_private_key alice global_sess_id.private_keys (PkDec "NSL.PublicKey") tr with
    | (None, tr) -> ()
    | (Some sk_a, tr) -> (
      match get_state alice sess_id tr with
      | (Some (InitiatorSentMsg1 bob n_a), tr) -> (
        decode_message2_proof tr alice bob msg sk_a n_a
      )
      | (_, tr) -> ()
    )
  )

val send_msg3_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg3 global_sess_id alice sess_id tr in
    trace_invariant tr_out
  ))
let send_msg3_proof tr global_sess_id alice sess_id =
  match get_state alice sess_id tr with
  | (Some (InitiatorSentMsg3 bob n_a n_b), tr) -> (
    match get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob tr with
    | (None, tr) -> ()
    | (Some pk_b, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label alice) 32 tr in
      compute_message3_proof tr alice bob pk_b n_b nonce
    )
  )
  | (_, tr) -> ()

val event_respond1_injective:
  tr:trace ->
  alice:principal -> alice':principal -> bob:principal ->
  n_a:bytes -> n_a':bytes -> n_b:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr bob (Respond1 alice bob n_a n_b) /\
    event_triggered tr bob (Respond1 alice' bob n_a' n_b)
  )
  (ensures
    alice == alice' /\
    n_a == n_a'
  )
let event_respond1_injective tr alice alice' bob n_a n_a' n_b = ()

#push-options "--z3rlimit 50"
val prepare_msg4:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> sess_id:state_id -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_sess_id, tr_out) = prepare_msg4 global_sess_id bob sess_id msg_id tr in
    trace_invariant tr_out
  ))
let prepare_msg4 tr global_sess_id bob sess_id msg_id =
  match recv_msg msg_id tr with
  | (None, tr) -> ()
  | (Some msg, tr) -> (
    match get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") tr with
    | (None, tr) -> ()
    | (Some sk_b, tr) -> (
      match get_state bob sess_id tr with
      | (Some (ResponderSentMsg2 alice n_a n_b), tr) -> (
        decode_message3_proof tr alice bob msg sk_b n_b;

        match decode_message3 alice bob msg sk_b n_b with
        | None -> ()
        | Some msg3 -> (
          // From the decode_message3 proof, we get the following fact:
          // exists alice' n_a'.
          //   get_label n_b `can_flow tr` (principal_label alice') /\
          //   event_triggered tr alice' nsl_event_tag (serialize nsl_event (Initiate2 alice' bob n_a' n_b))
          // We want to obtain the same fact, with the actual n_a (not the one from the exists, n_a'),
          // and the actual alice!
          // We prove it like this.
          // We know from the state predicate that the event Respond1 alice bob n_a n_b was triggered
          // Moreover, Initiate2 alice' bob n_a' n_b implies Respond1 alice' bob n_a' n_b (modulo corruption)
          // From the event predicate, we know that n_b was generated just before each Respond1 event
          // Hence the two Respond1 events are equal, and we get n_a == n_a' and alice == alice'
          // The fact that alice' knows n_b is used to show that if
          // principal_corrupt tr alice' \/ principal_corrupt tr bob
          // then
          // principal_corrupt tr alice \/ principal_corrupt tr bob
          // because we know the label of n_b (which is (join (principal_label alice) (principal_label bob))).
          // It is useful in the "modulo corruption" part of the proof.
          introduce (~((join (principal_label alice) (principal_label bob)) `can_flow tr` public)) ==> event_triggered tr alice (Initiate2 alice bob n_a n_b) with _. (
            assert(exists alice' n_a'. get_label tr n_b `can_flow tr` (principal_label alice') /\ event_triggered tr alice' (Initiate2 alice' bob n_a' n_b));
            eliminate exists alice' n_a'. get_label tr n_b `can_flow tr` (principal_label alice') /\ event_triggered tr alice' (Initiate2 alice' bob n_a' n_b)
            returns _
            with _. (
              event_respond1_injective tr alice alice' bob n_a n_a' n_b
            )
          )
        )
      )
      | (_, tr) -> ()
    )
  )
#pop-options
