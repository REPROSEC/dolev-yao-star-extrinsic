module DY.Example.BAN_CCITT_X509_3.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.BAN_CCITT_X509_3.Protocol.Total
open DY.Example.BAN_CCITT_X509_3.Protocol.Total.Proof
open DY.Example.BAN_CCITT_X509_3.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

#push-options "--ifuel 1"
let ban_ccitt_session_pred: local_state_predicate ban_ccitt_session = {
  pred = (fun tr prin sess_id st ->
    match st with
    | InitiatorSentMsg1 bob n_a x_a y_a -> (
      let alice = prin in
      is_publishable tr x_a /\
      is_publishable tr n_a /\
      is_knowable_by (ban_ccitt_label alice bob) tr y_a /\
      event_triggered tr alice (Initiate1 alice bob n_a x_a y_a)
    )
    | ResponderSentMsg2 alice n_b x_b y_b n_a -> (
      let bob = prin in
      is_publishable tr x_b /\ is_publishable tr n_a /\
      is_publishable tr n_b /\
      is_knowable_by (ban_ccitt_label alice bob) tr y_b /\
      event_triggered tr bob (Respond1 bob alice n_b x_b y_b n_a)
    )
    | InitiatorSentMsg3 bob n_b -> (
      let alice = prin in
      is_publishable tr n_b /\
      event_triggered tr alice (Initiate2 alice bob n_b)
    )
    | ResponderReceivedMsg3 alice n_b -> (
      let bob = prin in
      is_publishable tr n_b /\
      event_triggered tr bob (Respond2 bob alice n_b)
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}
#pop-options

#push-options "--ifuel 1"
let ban_ccitt_event_pred: event_predicate ban_ccitt_event =
  fun tr prin e ->
    match e with
    | Initiate1 alice bob n_a x_a y_a ->
      prin == alice /\
      is_publishable tr x_a /\
      is_publishable tr n_a /\
      is_knowable_by (ban_ccitt_label alice bob) tr y_a
    | Respond1 bob alice n_b x_b y_b n_a ->
      prin == bob /\
      is_publishable tr x_b /\ is_publishable tr n_a /\
      is_publishable tr n_b /\
      is_knowable_by (ban_ccitt_label alice bob) tr y_b
    | Initiate2 alice bob n_b ->
      prin == alice /\
      is_publishable tr n_b /\
      (is_corrupt tr (long_term_key_label bob) \/
        (exists x_b y_b n_a. event_triggered tr bob (Respond1 bob alice n_b x_b y_b n_a)))
    | Respond2 bob alice n_b ->
      prin == bob /\
      is_publishable tr n_b /\
      (is_corrupt tr (long_term_key_label alice) \/
        (event_triggered tr alice (Initiate2 alice bob n_b)))
#pop-options

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  mk_local_state_tag_and_pred ban_ccitt_session_pred;
]

let all_events = [
  mk_event_tag_and_pred ban_ccitt_event_pred;
]

let ban_ccitt_trace_invs: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance ban_ccitt_protocol_invs: protocol_invariants = {
  crypto_invs = ban_ccitt_crypto_invs;
  trace_invs = ban_ccitt_trace_invs;
}

let _ = do_split_boilerplate mk_state_pred_correct all_sessions
let _ = do_split_boilerplate mk_event_pred_correct all_events

(*** Proofs ****)

#push-options "--z3rlimit 1000 --ifuel 2 --fuel 1 --split_queries always"
val send_msg1_proof:
  global_sess_id:ban_ccitt_global_sess_ids -> alice:principal -> bob:principal -> x_a:bytes -> y_a:bytes -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    is_publishable tr x_a /\
    is_knowable_by (ban_ccitt_label alice bob) tr y_a
  )
  (ensures (
    let (_, tr_out) = send_msg1 global_sess_id alice bob x_a y_a tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (send_msg1 global_sess_id alice bob x_a y_a tr)]
let send_msg1_proof global_sess_id alice bob x_a y_a tr =
  reveal_opaque (`%send_msg1) (send_msg1 global_sess_id alice bob x_a y_a);
  let (alice_si, tr1) = new_session_id alice tr in
  let (n_a, tr2) = mk_rand NoUsage public 32 tr1 in
  let (pke_nonce, tr3) = mk_rand PkeNonce (long_term_key_label alice) 32 tr2 in
  let (sig_nonce, tr4) = mk_rand SigNonce (long_term_key_label alice) 32 tr3 in
  match get_public_key alice global_sess_id.pki (LongTermPkeKey "BAN_CCITT.PkeKey") bob tr4 with
  | (None, _) -> ()
  | (Some pk_b, tr5) -> (
    match get_private_key alice global_sess_id.private_keys (LongTermSigKey "BAN_CCITT.SigKey") tr5 with
    | (None, _) -> ()
    | (Some sk_a, tr6) -> (
      let (_, tr7) = trigger_event alice (Initiate1 alice bob n_a x_a y_a) tr6 in
      compute_message1_proof tr7 alice bob pk_b n_a x_a y_a pke_nonce sig_nonce sk_a
    )
  )
#pop-options

#push-options "--z3rlimit 1000 --ifuel 2 --fuel 1 --split_queries always"
val receive_msg1_send_msg2_proof:
  global_sess_id:ban_ccitt_global_sess_ids -> bob:principal -> alice:principal -> msg1_id:nat -> x_b:bytes -> y_b:bytes -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    is_publishable tr x_b /\
    is_knowable_by (ban_ccitt_label alice bob) tr y_b
  )
  (ensures (
    let (_, tr_out) = receive_msg1_send_msg2 global_sess_id bob alice msg1_id x_b y_b tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (receive_msg1_send_msg2 global_sess_id bob alice msg1_id x_b y_b tr)]
let receive_msg1_send_msg2_proof global_sess_id bob alice msg1_id x_b y_b tr =
  reveal_opaque (`%receive_msg1_send_msg2) (receive_msg1_send_msg2 global_sess_id bob alice msg1_id x_b y_b);
  match get_public_key bob global_sess_id.pki (LongTermSigKey "BAN_CCITT.SigKey") alice tr with
  | (None, _) -> ()
  | (Some vk_a, tr1) -> (
    match recv_msg msg1_id tr1 with
    | (None, _) -> ()
    | (Some msg1_bytes, tr2) -> (
      decode_message1_proof tr2 msg1_bytes bob alice vk_a;
      match decode_message1 msg1_bytes bob vk_a with
      | None -> ()
      | Some msg1 -> (
        let (bob_si, tr3) = new_session_id bob tr2 in
        let (n_b, tr4) = mk_rand NoUsage public 32 tr3 in
        let (pke_nonce, tr5) = mk_rand PkeNonce (long_term_key_label bob) 32 tr4 in
        let (sig_nonce, tr6) = mk_rand SigNonce (long_term_key_label bob) 32 tr5 in
        match get_public_key bob global_sess_id.pki (LongTermPkeKey "BAN_CCITT.PkeKey") alice tr6 with
        | (None, _) -> ()
        | (Some pk_a, tr7) -> (
          match get_private_key bob global_sess_id.private_keys (LongTermSigKey "BAN_CCITT.SigKey") tr7 with
          | (None, _) -> ()
          | (Some sk_b, tr8) -> (
            let (_, tr9) = trigger_event bob (Respond1 bob alice n_b x_b y_b msg1.m1_n_a) tr8 in
            compute_message2_proof tr9 bob alice pk_a n_b msg1.m1_n_a x_b y_b pke_nonce sig_nonce sk_b
          )
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 1000 --ifuel 2 --fuel 1 --split_queries always"
val receive_msg2_send_msg3_proof:
  global_sess_id:ban_ccitt_global_sess_ids -> alice:principal -> alice_si:state_id -> bob:principal -> msg2_id:nat -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = receive_msg2_send_msg3 global_sess_id alice alice_si bob msg2_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (receive_msg2_send_msg3 global_sess_id alice alice_si bob msg2_id tr)]
let receive_msg2_send_msg3_proof global_sess_id alice alice_si bob msg2_id tr =
  reveal_opaque (`%receive_msg2_send_msg3) (receive_msg2_send_msg3 global_sess_id alice alice_si bob msg2_id);
  allow_inversion ban_ccitt_session;
  match get_state alice alice_si tr with
  | (None, _) -> ()
  | (Some session_state, tr1) -> (
    if not (InitiatorSentMsg1? session_state) then () else (
      let InitiatorSentMsg1 bob_id n_a x_a y_a = session_state in
      if bob <> bob_id then () else (
        match get_public_key alice global_sess_id.pki (LongTermSigKey "BAN_CCITT.SigKey") bob tr1 with
        | (None, _) -> ()
        | (Some vk_b, tr2) -> (
          match recv_msg msg2_id tr2 with
          | (None, _) -> ()
          | (Some msg2_bytes, tr3) -> (
            decode_message2_proof tr3 msg2_bytes alice bob vk_b n_a;
            match decode_message2 msg2_bytes alice vk_b n_a with
            | None -> ()
            | Some msg2 -> (
              assert(is_publishable tr3 msg2.m2_n_b);
              assert(
                is_corrupt tr3 (long_term_key_label bob) \/
                (exists y_b. event_triggered tr3 bob (Respond1 bob alice msg2.m2_n_b msg2.m2_x_b y_b n_a))
              );
              let (sig_nonce, tr4) = mk_rand SigNonce (long_term_key_label alice) 32 tr3 in
              match get_private_key alice global_sess_id.private_keys (LongTermSigKey "BAN_CCITT.SigKey") tr4 with
              | (None, _) -> ()
              | (Some sk_a, tr5) -> (
                let (_, tr6) = trigger_event alice (Initiate2 alice bob msg2.m2_n_b) tr5 in
                compute_message3_proof tr6 alice bob msg2.m2_n_b sig_nonce sk_a
              )
            )
          )
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 1000 --ifuel 2 --fuel 1 --split_queries always"
val receive_msg3_proof:
  global_sess_id:ban_ccitt_global_sess_ids -> bob:principal -> bob_si:state_id -> alice:principal -> msg3_id:nat -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = receive_msg3 global_sess_id bob bob_si alice msg3_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (receive_msg3 global_sess_id bob bob_si alice msg3_id tr)]
let receive_msg3_proof global_sess_id bob bob_si alice msg3_id tr =
  reveal_opaque (`%receive_msg3) (receive_msg3 global_sess_id bob bob_si alice msg3_id);
  allow_inversion ban_ccitt_session;
  match get_state bob bob_si tr with
  | (None, _) -> ()
  | (Some session_state, tr1) -> (
    if not (ResponderSentMsg2? session_state) then () else (
      let ResponderSentMsg2 alice_id n_b x_b y_b n_a = session_state in
      if alice <> alice_id then () else (
        match get_public_key bob global_sess_id.pki (LongTermSigKey "BAN_CCITT.SigKey") alice tr1 with
        | (None, _) -> ()
        | (Some vk_a, tr2) -> (
          match recv_msg msg3_id tr2 with
          | (None, _) -> ()
          | (Some msg3_bytes, tr3) -> (
            decode_message3_proof tr3 msg3_bytes bob alice vk_a n_b;
            match decode_message3 msg3_bytes bob vk_a n_b with
            | None -> ()
            | Some msg3 -> (
              assert(is_publishable tr3 n_b);
              assert(is_corrupt tr3 (long_term_key_label alice) \/ event_triggered tr3 alice (Initiate2 alice bob n_b));
              ()
            )
          )
        )
      )
    )
  )
#pop-options
