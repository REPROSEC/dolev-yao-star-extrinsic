module DY.Example.AndrewRPC.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.AndrewRPC.Protocol.Total
open DY.Example.AndrewRPC.Protocol.Total.Proof
open DY.Example.AndrewRPC.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Invariants ***)

#push-options "--ifuel 2 --z3rlimit 50"
let andrew_rpc_session_pred: local_state_predicate andrew_rpc_session = {
  pred = (fun tr prin sess_id session ->
    match session with
    | InitiatorSentMsg1 bob n_a -> (
      is_publishable tr n_a /\
      event_triggered tr prin (Initiate1 prin bob n_a)
    )
    | InitiatorReceivedMsg2 bob n_a k_prime_ab -> (
      is_publishable tr n_a /\
      event_triggered tr prin (Initiate2 prin bob n_a) /\
      is_knowable_by (andrew_rpc_nonce_label prin bob) tr k_prime_ab /\
      (
        is_publishable tr k_prime_ab \/
        k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = prin; askd_bob = bob; askd_n_a = n_a}))
      )
    )
    | ResponderSentMsg2 alice n_a k_prime_ab -> (
      is_publishable tr n_a /\
      is_secret (andrew_rpc_session_key_label alice prin n_a) tr k_prime_ab /\
      k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = prin; askd_n_a = n_a})) /\
      event_triggered tr prin (Respond1 alice prin n_a k_prime_ab)
    )
    | ResponderReceivedMsg3 alice n_a k_prime_ab -> (
      is_publishable tr n_a /\
      is_secret (andrew_rpc_session_key_label alice prin n_a) tr k_prime_ab /\
      k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = prin; askd_n_a = n_a})) /\
      event_triggered tr prin (Respond2 alice prin n_a k_prime_ab)
    )
    | ResponderReceivedMsg1 alice n_a -> (
      is_publishable tr n_a
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id session -> ());
  pred_knowable = (fun tr prin sess_id session -> ());
}

let andrew_rpc_event_pred: event_predicate andrew_rpc_event =
  fun tr prin event ->
    match event with
    | Initiate1 alice bob n_a -> (
      prin == alice /\
      is_publishable tr n_a
    )
    | Respond1 alice bob n_a k_prime_ab -> (
      prin == bob /\
      is_publishable tr n_a /\
      is_secret (andrew_rpc_session_key_label alice bob n_a) tr k_prime_ab /\
      k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = n_a}))
    )
    | Initiate2 alice bob n_a -> (
      prin == alice /\
      event_triggered tr alice (Initiate1 alice bob n_a) /\
      (is_corrupt tr (andrew_rpc_nonce_label alice bob) \/ (
        exists k_prime_ab. event_triggered tr bob (Respond1 alice bob n_a k_prime_ab)
      ))
    )
    | Respond2 alice bob n_a k_prime_ab -> (
      prin == bob /\
      event_triggered tr bob (Respond1 alice bob n_a k_prime_ab) /\
      (is_corrupt tr (andrew_rpc_session_key_label alice bob n_a) \/ (
        event_triggered tr alice (Initiate2 alice bob n_a)
      ))
    )
#pop-options

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  mk_local_state_tag_and_pred andrew_rpc_session_pred;
]

let all_events = [
  mk_event_tag_and_pred andrew_rpc_event_pred;
]

let andrew_rpc_trace_invs: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_andrew_rpc : protocol_invariants = {
  crypto_invs = crypto_invariants_andrew_rpc;
  trace_invs = andrew_rpc_trace_invs;
}

let _ = do_split_boilerplate mk_state_pred_correct all_sessions
let _ = do_split_boilerplate mk_event_pred_correct all_events

(*** Helper predicates ***)

val is_kab_for: trace -> bytes -> principal -> principal -> prop
let is_kab_for tr kab alice bob =
  kab `has_usage tr` (AeadKey andrew_rpc_kab_tag (serialize _ {akd_alice = alice; akd_bob = bob})) /\
  is_secret (andrew_rpc_nonce_label alice bob) tr kab

(*** Proofs ***)

#push-options "--z3rlimit 50"
val alice_send_msg1_proof:
  alice:principal -> bob:principal -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let ((sid, msg_id), tr_out) = alice_send_msg1 alice bob tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (alice_send_msg1 alice bob tr)]
let alice_send_msg1_proof alice bob tr =
  reveal_opaque (`%alice_send_msg1) (alice_send_msg1 alice bob tr);
  let (sid, tr0) = new_session_id alice tr in
  let (n_a, tr1) = mk_rand NoUsage public 32 tr0 in
  let ((), tr2) = trigger_event alice (Initiate1 alice bob n_a) tr1 in
  let ((), tr3) = set_state alice sid (InitiatorSentMsg1 bob n_a) tr2 in
  compute_message1_proof tr3 alice n_a;
  ()
#pop-options

#push-options "--z3rlimit 100 --split_queries always"
val bob_recv_msg1_send_msg2_proof:
  bob:principal -> alice:principal -> kab:bytes -> msg1_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    is_kab_for tr kab alice bob
  )
  (ensures (
    let (opt_res, tr_out) = bob_recv_msg1_send_msg2 bob alice kab msg1_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (bob_recv_msg1_send_msg2 bob alice kab msg1_id tr); SMTPat (is_kab_for tr kab alice bob)]
let bob_recv_msg1_send_msg2_proof bob alice kab msg1_id tr =
  reveal_opaque (`%bob_recv_msg1_send_msg2) (bob_recv_msg1_send_msg2 bob alice kab msg1_id tr);
  match recv_msg msg1_id tr with
  | (None, _) -> ()
  | (Some msg1_bytes, tr0) -> (
    decode_message1_proof tr0 msg1_bytes;
    match decode_message1 msg1_bytes with
    | None -> ()
    | Some (alice_recv, n_a) -> (
      if alice = alice_recv then (
        let (sid, tr1) = new_session_id bob tr0 in
        let (k_prime_ab, tr2) = mk_rand (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = n_a})) (andrew_rpc_session_key_label alice bob n_a) 32 tr1 in
        let (nonce, tr3) = mk_rand NoUsage public 12 tr2 in
        let ((), tr4) = trigger_event bob (Respond1 alice bob n_a k_prime_ab) tr3 in
        let ((), tr5) = set_state bob sid (ResponderSentMsg2 alice n_a k_prime_ab) tr4 in
        compute_message2_proof tr5 alice bob kab n_a k_prime_ab nonce;
        ()
      ) else ()
    )
  )
#pop-options

#push-options "--z3rlimit 400 --ifuel 2"
val alice_recv_msg2_send_msg3_proof:
  alice:principal -> bob:principal -> sid:state_id -> kab:bytes -> msg2_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    is_kab_for tr kab alice bob
  )
  (ensures (
    let (opt_res, tr_out) = alice_recv_msg2_send_msg3 alice bob sid kab msg2_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (alice_recv_msg2_send_msg3 alice bob sid kab msg2_id tr); SMTPat (is_kab_for tr kab alice bob)]
let alice_recv_msg2_send_msg3_proof alice bob sid kab msg2_id tr =
  reveal_opaque (`%alice_recv_msg2_send_msg3) (alice_recv_msg2_send_msg3 alice bob sid kab msg2_id tr);
  match get_state alice sid tr with
  | (Some (InitiatorSentMsg1 bob_sess n_a), tr) -> (
    if bob_sess = bob then (
      match recv_msg msg2_id tr with
      | (Some msg2_bytes, tr) -> (
        decode_message2_proof tr alice bob kab msg2_bytes;
        match decode_message2 kab msg2_bytes with
        | Some msg2 -> (
          if msg2.m2_n_a = n_a && msg2.m2_bob = bob then (
            let ((), tr_a) = trigger_event alice (Initiate2 alice bob n_a) tr in
            let ((), tr_b) = set_state alice sid (InitiatorReceivedMsg2 bob n_a msg2.m2_k_prime_ab) tr_a in
            let (nonce3, tr_c) = mk_rand NoUsage public 12 tr_b in
            mk_rand_bytes_invariant NoUsage public 12 tr_b;
            mk_rand_get_label NoUsage public 12 tr_b;
            compute_message3_proof tr_c alice bob n_a msg2.m2_k_prime_ab nonce3
          ) else ()
        )
        | None -> ()
      )
      | (None, _) -> ()
    ) else ()
  )
  | _ -> ()
#pop-options

#push-options "--z3rlimit 400 --ifuel 2 --split_queries always"
val bob_recv_msg3_send_msg4_proof:
  bob:principal -> sid:state_id -> msg3_id:nat -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_res, tr_out) = bob_recv_msg3_send_msg4 bob sid msg3_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (bob_recv_msg3_send_msg4 bob sid msg3_id tr)]
let bob_recv_msg3_send_msg4_proof bob sid msg3_id tr =
  reveal_opaque (`%bob_recv_msg3_send_msg4) (bob_recv_msg3_send_msg4 bob sid msg3_id tr);
  match get_state bob sid tr with
  | (Some (ResponderSentMsg2 alice n_a k_prime_ab), tr) -> (
    match recv_msg msg3_id tr with
    | (Some msg3_bytes, tr) -> (
      decode_message3_proof tr alice bob n_a k_prime_ab msg3_bytes;
      match decode_message3 k_prime_ab msg3_bytes with
      | Some msg3 -> (
        if msg3.m3_n_a = n_a then (
          let ((), tr_e) = trigger_event bob (Respond2 alice bob n_a k_prime_ab) tr in
          let ((), tr_s) = set_state bob sid (ResponderReceivedMsg3 alice n_a k_prime_ab) tr_e in
          let (n_b, tr_r) = mk_rand NoUsage public 32 tr_s in
          mk_rand_bytes_invariant NoUsage public 32 tr_s;
          mk_rand_get_label NoUsage public 32 tr_s;
          assert(is_publishable tr_r n_b);
          compute_message4_proof tr_r n_b
        ) else ()
      )
      | None -> ()
    )
    | (None, _) -> ()
  )
  | _ -> ()
#pop-options
