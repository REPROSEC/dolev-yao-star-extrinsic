module DY.Example.DH.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total
open DY.Example.DH.Protocol.Total.Proof
open DY.Example.DH.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

/// The (local) state predicate.

val is_dh_shared_key: trace -> principal -> principal -> bytes -> prop
let is_dh_shared_key tr alice bob k = exists si sj.
  // We are using the equivalent relation here because depending on the party we are looking at
  // the label is either ``join (principal_state_label alice si) (principal_state_label bob sj)`` or
  // ``join (principal_state_label bob sj) (principal_state_label alice si)``.
  // This is because k is either build from ``dh x (dh_pk y)`` or ``dh y (dh_pk x)``.
  get_label k `equivalent tr` join (principal_state_label alice si) (principal_state_label bob sj) /\ 
  get_usage k == AeadKey "DH.aead_key"

let dh_session_pred: local_state_predicate dh_session = {
  pred = (fun tr prin sess_id st ->
    match st with
    | InitiatorSentMsg1 bob x -> (
      let alice = prin in
      is_secret (principal_state_label alice sess_id) tr x /\
      get_usage x == DhKey "DH.dh_key" /\
      event_triggered tr alice (Initiate1 alice bob x)
    )
    | ResponderSentMsg2 alice gx gy y -> (
      let bob = prin in
      is_publishable tr gx /\ is_publishable tr gy /\
      is_secret (principal_state_label bob sess_id) tr y /\ get_usage y  == DhKey "DH.dh_key" /\
      gy == dh_pk y /\
      event_triggered tr bob (Respond1 alice bob gx gy y)
    )
    | InitiatorSendMsg3 bob gx gy k -> (
      let alice = prin in
      is_publishable tr gx /\ is_publishable tr gy /\
      is_knowable_by (principal_state_label alice sess_id) tr k /\
      event_triggered tr alice (Initiate2 alice bob gx gy k) /\
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
      (exists y. k == dh y gx /\ is_dh_shared_key tr alice bob k /\ 
        event_triggered tr bob (Respond1 alice bob gx gy y)))
    )
    | ResponderReceivedMsg3 alice gx gy k -> (
      let bob = prin in
      is_publishable tr gx /\ is_publishable tr gy /\
      is_knowable_by (principal_state_label bob sess_id) tr k /\
      event_triggered tr bob (Respond2 alice bob gx gy k) /\
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
        (is_dh_shared_key tr alice bob k /\ 
        event_triggered tr alice (Initiate2 alice bob gx gy k)))
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}

/// The (local) event predicate.

let dh_event_pred: event_predicate dh_event =
  fun tr prin e ->
    match e with
    | Initiate1 alice bob x -> True
    | Respond1 alice bob gx gy y -> (
      is_publishable tr gx /\ is_publishable tr gy /\
      (exists sess_id. is_secret (principal_state_label bob sess_id) tr y) /\
      get_usage y == DhKey "DH.dh_key" /\
      gy = dh_pk y
    )
    | Initiate2 alice bob gx gy k -> (
      is_publishable tr gx /\ is_publishable tr gy /\
      (exists x sess_id. is_secret (principal_state_label alice sess_id) tr x /\
      gx = dh_pk x /\ k == dh x gy) /\
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
        (exists y. k == dh y gx /\ is_dh_shared_key tr alice bob k /\ event_triggered tr bob (Respond1 alice bob gx gy y)))
    )
    | Respond2 alice bob gx gy k -> (
      is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
      (is_dh_shared_key tr alice bob k /\
        event_triggered tr alice (Initiate2 alice bob gx gy k))
    )

/// List of all local state predicates.

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (local_state_dh_session.tag, local_state_predicate_to_local_bytes_state_predicate dh_session_pred);
]

/// List of all local event predicates.

let all_events = [
  (dh_event_instance.tag, compile_event_pred dh_event_pred)
]

/// Create the global trace invariants.

let dh_trace_invs: trace_invariants (dh_crypto_invs) = {
  state_pred = mk_state_predicate dh_crypto_invs all_sessions;
  event_pred = mk_event_pred all_events;
}

instance dh_protocol_invs: protocol_invariants = {
  crypto_invs = dh_crypto_invs;
  trace_invs = dh_trace_invs;
}

/// Lemmas that the global state predicate contains all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate dh_protocol_invs) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  mk_global_local_bytes_state_predicate_correct dh_protocol_invs all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate dh_protocol_invs) all_sessions)

val full_dh_session_pred_has_pki_invariant: squash (has_pki_invariant dh_protocol_invs)
let full_dh_session_pred_has_pki_invariant = all_sessions_has_all_sessions ()

val full_dh_session_pred_has_private_keys_invariant: squash (has_private_keys_invariant dh_protocol_invs)
let full_dh_session_pred_has_private_keys_invariant = all_sessions_has_all_sessions ()

val full_dh_session_pred_has_dh_invariant: squash (has_local_state_predicate dh_protocol_invs dh_session_pred)
let full_dh_session_pred_has_dh_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred dh_protocol_invs) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct dh_protocol_invs all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred dh_protocol_invs) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred dh_protocol_invs) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred dh_protocol_invs) all_events))

val full_dh_event_pred_has_dh_invariant: squash (has_event_pred dh_protocol_invs dh_event_pred)
let full_dh_event_pred_has_dh_invariant = all_events_has_all_events ()

(*** Proofs ****)

val prepare_msg1_proof:
  tr:trace ->
  alice:principal -> bob:principal ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (sess_id, tr_out) = prepare_msg1 alice bob tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant (snd (prepare_msg1 alice bob tr)))]
let prepare_msg1_proof tr alice bob = ()

val send_msg1_proof:
  tr:trace ->
  alice:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (msg_id, tr_out) = send_msg1 alice sess_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant (snd (send_msg1 alice sess_id tr)))]
let send_msg1_proof tr alice sess_id =
  match get_state alice sess_id tr with
  | (Some (InitiatorSentMsg1 bob x), tr) -> (
    compute_message1_proof tr alice bob x sess_id
  )
  | _ -> ()

val prepare_msg2_proof:
  tr:trace ->
  alice:principal -> bob:principal -> msg_id:nat ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (msg_id, tr_out) = prepare_msg2 alice bob msg_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant (snd (prepare_msg2 alice bob msg_id tr)))]
let prepare_msg2_proof tr alice bob msg_id =
  match recv_msg msg_id tr with
  | (Some msg, tr) -> (
    decode_message1_proof tr alice bob msg
  )
  | (None, tr) -> ()

val send_msg2_proof:
  tr:trace ->
  global_sess_id:dh_global_sess_ids -> bob:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (msg_id, tr_out) = send_msg2 global_sess_id bob sess_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant (snd (send_msg2 global_sess_id bob sess_id tr)))]
let send_msg2_proof tr global_sess_id bob sess_id =
  match get_state bob sess_id tr with
  | (Some (ResponderSentMsg2 alice gx gy y), tr) -> (
    match get_private_key bob global_sess_id.private_keys (Sign "DH.SigningKey") tr with
    | (Some sk_b, tr) -> (
      let (n_sig, tr) = mk_rand SigNonce (principal_label bob) 32 tr in
      compute_message2_proof tr sess_id alice bob {alice; gx} y sk_b n_sig
    )
    | (None, tr) -> ()
  )
  | _ -> ()

val prepare_msg3_proof:
  tr:trace ->
  global_sess_id:dh_global_sess_ids -> alice:principal -> bob:principal -> msg_id:nat -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = prepare_msg3 global_sess_id alice bob msg_id sess_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant (snd (prepare_msg3 global_sess_id alice bob msg_id sess_id tr)))]
let prepare_msg3_proof tr global_sess_id alice bob msg_id sess_id =
  match get_state alice sess_id tr with
  | (Some (InitiatorSentMsg1 bob x), tr) -> (
    match recv_msg msg_id tr with
    | (Some msg_bytes, tr) -> (
      match get_public_key alice global_sess_id.pki (Verify "DH.SigningKey") bob tr with
      | (Some pk_b, tr) -> (
        let gx = dh_pk x in
        match decode_message2 msg_bytes alice gx pk_b with
        | Some msg2 -> (
          decode_message2_proof tr alice bob msg_bytes gx pk_b;
          let k = dh x msg2.gy in
          assert(is_publishable tr gx);
          assert(is_publishable tr msg2.gy);
          assert(is_knowable_by (principal_state_label alice sess_id) tr k);

          assert((exists x sess_id. is_secret (principal_state_label alice sess_id) tr x /\
            gx = dh_pk x));
          assert(get_usage k = AeadKey "DH.aead_key");
          assert(exists si. is_knowable_by (principal_state_label alice si) tr k);

          let alice_and_bob_not_corrupt = (~(is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob))) in
          let dh_key_and_event_respond1 = (exists y. k == dh y gx /\ is_dh_shared_key tr alice bob k /\ event_triggered tr bob (Respond1 alice bob gx msg2.gy y)) in
          introduce alice_and_bob_not_corrupt ==> dh_key_and_event_respond1 
          with _. (
            assert(exists y k'. k' == dh y gx /\ msg2.gy == dh_pk y /\ event_triggered tr bob (Respond1 alice bob gx msg2.gy y));
            eliminate exists y k'. k' == dh y gx /\ event_triggered tr bob (Respond1 alice bob gx msg2.gy y)
            returns dh_key_and_event_respond1
            with _. (
              assert(event_triggered tr bob (Respond1 alice bob gx msg2.gy y));
              
              assert(dh_pk y == msg2.gy);
              assert(dh_pk x = gx);              
              dh_shared_secret_lemma x y;
              assert(dh y gx == dh x msg2.gy);
              assert(k == k');
              
              assert(exists si sj. get_label k `equivalent tr` join (principal_state_label alice si) (principal_state_label bob sj));

              assert(dh_key_and_event_respond1);
              ()
            )
          )
        )
        | None -> ()
      )
      | (None, tr) -> ()
    )
    | (None, tr) -> ()
  )
  | _ -> ()

val send_msg3_proof:
  tr:trace ->
  global_sess_id:dh_global_sess_ids -> alice:principal -> bob:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = send_msg3 global_sess_id alice bob sess_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant (snd (send_msg3 global_sess_id alice bob sess_id tr)))]
let send_msg3_proof tr global_sess_id alice bob sess_id =
  match get_state alice sess_id tr with
  | (Some (InitiatorSendMsg3 bob gx gy k), tr) -> (
    match get_private_key alice global_sess_id.private_keys (Sign "DH.SigningKey") tr with
    | (Some sk_a, tr) -> (
      let (n_sig, tr) = mk_rand SigNonce (principal_label alice) 32 tr in

      // The following code is not needed for the proof.
      // It just shows what we need to show to prove the lemma.
      assert(event_triggered tr alice (Initiate2 alice bob gx gy k));
      assert(exists x. event_triggered tr alice (Initiate2 alice bob gx gy (dh x gy)) /\ gx = dh_pk x);

      compute_message3_proof tr alice bob gx gy sk_a n_sig;
      ()
    )
    | (None, tr) -> ()
  )
  | _ -> ()

#set-options "--z3rlimit 50"
val verify_msg3_proof:
  tr:trace ->
  global_sess_id:dh_global_sess_ids -> alice:principal -> bob:principal -> msg_id:nat -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = verify_msg3 global_sess_id alice bob msg_id sess_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant (snd (verify_msg3 global_sess_id alice bob msg_id sess_id tr)))]
let verify_msg3_proof tr global_sess_id alice bob msg_id sess_id =
  match get_state bob sess_id tr with
  | (Some (ResponderSentMsg2 alice gx gy y), tr) -> (
    match recv_msg msg_id tr with
    | (Some msg_bytes, tr) -> (
      match get_public_key bob global_sess_id.pki (Verify "DH.SigningKey") alice tr with
      | (Some pk_a, tr) -> (
          decode_message3_proof tr alice bob gx gy msg_bytes pk_a;
          
          match decode_message3 msg_bytes bob gx gy pk_a with
          | Some msg3 -> (
            
            let k = dh y gx in

            assert(event_triggered tr bob (Respond1 alice bob gx gy y));
            // The decode_message3_proof gives us that there exists a k' such that 
            // the event Initiate2 has been triggered or alice is corrupt.
            // On a high level we need to show now that this event was triggered
            // for our concrete k.
            assert(exists x. gx == dh_pk x /\ event_triggered tr alice (Initiate2 alice bob gx gy (dh x gy)) \/ is_corrupt tr (principal_label alice));

            // Proof strategy: We want to work without the corruption case
            // so we introduce this implication.
            let alice_and_bob_not_corrupt = (~(is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob))) in
            let event_initiate2 = event_triggered tr alice (Initiate2 alice bob gx gy k) in
            introduce alice_and_bob_not_corrupt ==> event_initiate2
            with _. (
              // We can now assert that there exists a x such that the event Initiate2 has been triggered
              // without the corruption case.
              assert(exists x. gx == dh_pk x /\ event_triggered tr alice (Initiate2 alice bob gx gy (dh x gy)));
              // We now introduce x to concretely reason about it.
              eliminate exists x. gx == dh_pk x /\ event_triggered tr alice (Initiate2 alice bob gx gy (dh x gy))
              returns event_initiate2
              with _. (
                // We use commutativity of DH to reconcile the (dh x gy) in our hypothesis,
                // and the (dh y gx) in event_initiate2
                dh_shared_secret_lemma x y
              )
            );

            assert(is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/ 
              (exists si sj. get_label k `equivalent tr` join (principal_state_label alice si) (principal_state_label bob sj)));
            assert(get_usage k == AeadKey "DH.aead_key");
            assert(is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
              (is_dh_shared_key tr alice bob k /\ event_triggered tr alice (Initiate2 alice bob gx gy k)));
            ()
          )
          | None -> ()
        )
        | (None, tr) -> ()
      )
      | (None, tr) -> ()
    )
  | (_, tr) -> ()
