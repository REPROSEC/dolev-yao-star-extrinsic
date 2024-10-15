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
    | InitiatorSendingMsg1 bob n_a -> (
      let alice = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_secret (join (principal_label alice) (principal_label bob)) tr n_a /\
      0 < DY.Core.Trace.Base.length tr /\
      rand_generated_before tr n_a
    )
    | ResponderSendingMsg2 alice n_a n_b -> (
      let bob = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_b /\
      
      event_triggered tr bob (Responding alice bob n_a n_b)
      // is_secret (join (principal_label alice) (principal_label bob)) tr n_b /\
      //  0 < DY.Core.Trace.Base.length tr /\
      // rand_generated_before tr n_b
    )
    | InitiatorSendingMsg3 bob n_a n_b  -> (
      let alice = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
       is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_b /\
      
      state_was_set_some_id tr alice (InitiatorSendingMsg1 bob n_a) /\
      ( is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob)
      \/ (
        state_was_set_some_id #_ tr bob (ResponderSendingMsg2 alice n_a n_b)
        ))
    )
    | ResponderReceivedMsg3 alice n_a n_b -> (
      let bob = prin in
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by (join (principal_label alice) (principal_label bob)) tr n_b /\
      state_was_set_some_id tr bob (ResponderSendingMsg2 alice n_a n_b) /\
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) 
      \/
      state_was_set_some_id #_ tr alice (InitiatorSendingMsg3 bob n_a n_b)
    )
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}

/// List of all local state predicates.

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (local_state_nsl_session.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_nsl);
]

/// The (local) event predicate.

let event_predicate_nsl: event_predicate nsl_event =
  fun tr prin e ->
    match e with    
    | Responding alice bob n_a n_b -> (
      prin == bob /\
      is_secret (join (principal_label alice) (principal_label bob)) tr n_b /\
      0 < DY.Core.Trace.Base.length tr /\
      rand_generated_at tr (DY.Core.Trace.Base.length tr - 1) n_b
    )
   
    
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
  | (Some (InitiatorSendingMsg1 bob n_a), tr) -> (
    match get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob tr with
    | (None, tr) -> ()
    | (Some pk_b, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label alice) 32 tr in
      compute_message1_proof tr alice bob pk_b n_a nonce
    )
  )
  | _ -> ()

val send_msg1__proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> bob:principal ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg1_ global_sess_id alice bob tr in
    trace_invariant tr_out
  ))
let send_msg1__proof tr global_sess_id alice bob =
  let (n_a, tr) = mk_rand NoUsage (join (principal_label alice) (principal_label bob)) 32 tr in
  
  let (sess_id, _) = new_session_id alice tr in
  let st = InitiatorSendingMsg1 bob n_a in
  let (_ , tr_state) = set_state alice sess_id st tr in

  match get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob tr_state with
    | (None, tr) -> ()
    | (Some pk_b, tr) -> (
    
      let (nonce, tr) = mk_rand PkNonce (principal_label alice) 32 tr in
      compute_message1_proof tr alice bob pk_b n_a nonce;
      
  ()
    )

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
  | (Some (ResponderSendingMsg2 alice n_a n_b), tr) -> (
    match get_public_key bob global_sess_id.pki (PkEnc "NSL.PublicKey") alice tr with
    | (None, tr) -> ()
    | (Some pk_a, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label bob) 32 tr in
      compute_message2_proof tr bob {n_a; alice;} pk_a n_b nonce
    )
  )
  | (_, tr) -> ()

val send_msg2__proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_ids, tr_out) = send_msg2_ global_sess_id bob msg_id tr in
    trace_invariant tr_out
  ))
let send_msg2__proof tr global_sess_id bob msg_id =
  match recv_msg msg_id tr with
  | (None, tr) -> ()
  | (Some msg, tr) -> (
    match get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") tr with
    | (None, tr) -> ()
    | (Some sk_b, tr) -> (
      decode_message1_proof tr bob msg sk_b;
      match decode_message1 bob msg sk_b with
      | None -> ()
      | Some msg1 -> (
      let alice = msg1.alice in
      let n_a = msg1.n_a in
    let (n_b, tr) = mk_rand NoUsage (join (principal_label msg1.alice) (principal_label bob)) 32 tr in
    let (_, tr) = trigger_event bob (Responding alice bob n_a n_b) tr in
    let st = ResponderSendingMsg2 msg1.alice msg1.n_a n_b in
    let (sess_id, _) = new_session_id bob tr in
    let (_, tr_st) = set_state bob sess_id st tr in
    match get_public_key bob global_sess_id.pki (PkEnc "NSL.PublicKey") alice tr_st with
    | (None, tr) -> ()
    | (Some pk_a, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label bob) 32 tr in
      compute_message2_proof tr bob {n_a; alice;} pk_a n_b nonce
    )
  ))
  )

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
      | (Some (InitiatorSendingMsg1 bob n_a), tr) -> (
                decode_message2_proof tr alice bob msg sk_a n_a
      )
      | (_, tr) -> ()
    )
  )

val prepare_msg3__proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_sess_id, tr_out) = prepare_msg3_ global_sess_id alice msg_id tr in
    trace_invariant tr_out
  ))
let prepare_msg3__proof tr global_sess_id alice msg_id =
  match recv_msg msg_id tr with
  | (None, tr) -> ()
  | (Some msg, tr) -> (
    match get_private_key alice global_sess_id.private_keys (PkDec "NSL.PublicKey") tr with
    | (None, tr) -> ()
    | (Some sk_a, tr) -> (
        match decode_message2_ alice msg sk_a with
        | None -> ()
        | Some msg2 ->
        let p = (fun (s:nsl_session) -> 
    (InitiatorSendingMsg1? s) && 
    (InitiatorSendingMsg1?.n_a s = msg2.n_a) && 
    (InitiatorSendingMsg1?.b s = msg2.bob))  in
        match lookup_state alice p tr with
        | (None , _) -> ()
        | (Some (st, sid) , _ ) ->
                decode_message2_proof tr alice msg2.bob msg sk_a msg2.n_a
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
  | (Some (InitiatorSendingMsg3 bob n_a n_b), tr) -> (
    match get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob tr with
    | (None, tr) -> ()
    | (Some pk_b, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label alice) 32 tr in
      compute_message3_proof tr alice bob pk_b n_b nonce
    )
  )
  | (_, tr) -> ()



val send_msg3__proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_ids, tr_out) = send_msg3_ global_sess_id alice msg_id tr in
    trace_invariant tr_out
  ))
let send_msg3__proof tr global_sess_id alice msg_id =
    match recv_msg msg_id tr with
  | (None, tr) -> ()
  | (Some msg, tr) -> (
    match get_private_key alice global_sess_id.private_keys (PkDec "NSL.PublicKey") tr with
    | (None, tr) -> ()
    | (Some sk_a, tr) -> (
        match decode_message2_ alice msg sk_a with
        | None -> ()
        | Some msg2 -> (
        let p = (fun (s:nsl_session) -> 
    (InitiatorSendingMsg1? s) && 
    (InitiatorSendingMsg1?.n_a s = msg2.n_a) && 
    (InitiatorSendingMsg1?.b s = msg2.bob))  in
        match lookup_state alice p tr with
        | (None , _) -> ()
        | (Some (st, sid) , _ ) -> (
                decode_message2_proof tr alice msg2.bob msg sk_a msg2.n_a;
        let n_b = msg2.n_b in
        let InitiatorSendingMsg1 bob n_a = st in
        let new_st = InitiatorSendingMsg3 bob n_a n_b in
        let (_, tr_state) = set_state alice sid new_st tr in
    match get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob tr_state with
    | (None, tr) -> ()
    | (Some pk_b, tr) -> (
      let (nonce, tr) = mk_rand PkNonce (principal_label alice) 32 tr in
      compute_message3_proof tr alice bob pk_b n_b nonce
    )
  ))
 ))


val event_respond1_injective:
  tr:trace ->
  alice:principal -> alice':principal -> bob:principal ->
  n_a:bytes -> n_a':bytes -> n_b:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr bob (Responding alice bob n_a n_b) /\
    event_triggered tr bob (Responding alice' bob n_a' n_b)
  )
  (ensures
    alice == alice' /\
    n_a == n_a'
  )
let event_respond1_injective tr alice alice' bob n_a n_a' n_b = ()

val receive_msg3_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> sess_id:state_id -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_sess_id, tr_out) = receive_msg3 global_sess_id bob msg_id tr in
    trace_invariant tr_out
  ))
let receive_msg3_proof tr global_sess_id bob sess_id msg_id =
  match recv_msg msg_id tr with
  | (None, tr) -> ()
  | (Some msg, tr) -> (
    match get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") tr with
    | (None, tr) -> ()
    | (Some sk_b, tr) -> (
        match decode_message3_ msg sk_b with
        | None -> ()
        | Some msg3 -> (
            let p = (fun (s:nsl_session) -> 
    (ResponderSendingMsg2? s) && 
    (ResponderSendingMsg2?.n_b s = msg3.n_b)) in
           match lookup_state bob p tr with
           | (None, _ ) -> ()
           | (Some (st, id), _) ->  (
           let ResponderSendingMsg2 alice n_a n_b = st in
            assert(event_triggered tr bob (Responding alice bob n_a n_b));
             
            assert(is_publishable tr n_b ==> is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob));
            introduce ~(is_publishable tr n_b) ==> 
            state_was_set_some_id tr alice (InitiatorSendingMsg3 bob n_a n_b)
            with _. (
              decode_message3__proof tr alice bob msg sk_b;
              eliminate exists alice' n_a'. get_label tr n_b `can_flow tr` (principal_label alice') /\ 
              state_was_set_some_id tr alice' (InitiatorSendingMsg3 bob n_a' n_b)
              returns _
              with _. (
                assert(event_triggered tr bob (Responding alice' bob n_a' n_b));
                event_respond1_injective tr alice alice' bob n_a n_a' n_b
              
              )

            )
           )
   )))
