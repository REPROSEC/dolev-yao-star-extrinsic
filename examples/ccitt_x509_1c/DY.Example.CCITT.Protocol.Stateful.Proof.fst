module DY.Example.CCITT.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.CCITT.Protocol.Total
open DY.Example.CCITT.Protocol.Total.Proof
open DY.Example.CCITT.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

#push-options "--ifuel 1"
let event_predicate_ccitt: event_predicate ccitt_event =
  fun tr prin e ->
    match e with
    | AliceSends alice bob ta na xa ya ->
      prin == alice /\
      is_publishable tr ta /\
      is_publishable tr na /\
      is_publishable tr xa /\
      is_knowable_by (ccitt_label alice bob) tr ya
    | BobReceives alice bob ta na xa ya ->
      prin == bob /\
      is_publishable tr ta /\
      is_publishable tr na /\
      is_publishable tr xa /\
      is_knowable_by (long_term_key_label bob) tr ya /\
      (is_corrupt tr (ccitt_label alice bob) \/
       event_triggered tr alice (AliceSends alice bob ta na xa ya))
#pop-options

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
]

let all_events = [
  mk_event_tag_and_pred event_predicate_ccitt;
]

let trace_invariants_ccitt: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_ccitt : protocol_invariants = {
  trace_invs = trace_invariants_ccitt;
  crypto_invs = crypto_invariants_ccitt;
}

let _ = do_split_boilerplate mk_state_pred_correct all_sessions
let _ = do_split_boilerplate mk_event_pred_correct all_events

(*** Proofs ***)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 2 --split_queries always"
val alice_send_msg1_proof:
  pki:state_id -> private_keys:state_id ->
  alice:principal -> bob:principal ->
  ta:bytes -> xa:bytes -> ya:bytes ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    is_publishable tr ta /\
    is_publishable tr xa /\
    is_knowable_by (ccitt_label alice bob) tr ya
  )
  (ensures (
    match alice_send_msg1 pki private_keys alice bob ta xa ya tr with
    | (Some msg_id, tr_out) -> trace_invariant tr_out
    | (None, tr_out) -> trace_invariant tr_out
  ))
  [SMTPat (alice_send_msg1 pki private_keys alice bob ta xa ya tr)]
let alice_send_msg1_proof pki private_keys alice bob ta xa ya tr =
  reveal_opaque (`%alice_send_msg1) (alice_send_msg1 pki private_keys alice bob ta xa ya tr);
  match get_private_key alice private_keys (LongTermSigKey ccitt_sign_tag) tr with
  | (None, _) -> ()
  | (Some sk_a, tr0) -> (
    match get_public_key alice pki (LongTermPkeKey ccitt_pke_tag) bob tr0 with
    | (None, _) -> ()
    | (Some pk_b, tr1) -> (
      let (na, tr2) = mk_rand NoUsage public 32 tr1 in
      let (n_inner_sig, tr3) = mk_rand SigNonce (long_term_key_label alice) 32 tr2 in
      let (n_inner_pke, tr4) = mk_rand PkeNonce (long_term_key_label alice) 32 tr3 in
      let (n_outer, tr5) = mk_rand SigNonce (long_term_key_label alice) 32 tr4 in
      let ((), tr6) = trigger_event alice (AliceSends alice bob ta na xa ya) tr5 in
      compute_message1_proof tr6 ta na bob xa ya pk_b sk_a n_inner_sig n_inner_pke n_outer alice
    )
  )
#pop-options

#push-options "--z3rlimit 600 --fuel 1 --ifuel 2 --split_queries always"
val bob_receive_msg1_proof:
  pki:state_id -> private_keys:state_id ->
  bob:principal -> alice:principal ->
  msg1_id:timestamp ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    match bob_receive_msg1 pki private_keys bob alice msg1_id tr with
    | (Some (), tr_out) -> trace_invariant tr_out
    | (None, tr_out) -> trace_invariant tr_out
  ))
  [SMTPat (bob_receive_msg1 pki private_keys bob alice msg1_id tr)]
let bob_receive_msg1_proof pki private_keys bob alice msg1_id tr =
  reveal_opaque (`%bob_receive_msg1) (bob_receive_msg1 pki private_keys bob alice msg1_id tr);
  match get_private_key bob private_keys (LongTermPkeKey ccitt_pke_tag) tr with
  | (None, _) -> ()
  | (Some sk_b, tr0) -> (
    match get_public_key bob pki (LongTermSigKey ccitt_sign_tag) alice tr0 with
    | (None, _) -> ()
    | (Some vk_a, tr1) -> (
      match recv_msg msg1_id tr1 with
      | (None, _) -> ()
      | (Some msg1_bytes, tr2) -> (
        decode_message1_proof tr2 bob msg1_bytes sk_b vk_a alice;
        match decode_message1 bob msg1_bytes sk_b vk_a with
        | None -> ()
        | Some (ta, na, bob', xa, ya) -> (
          if bob' = bob then ()
          else ()
        )
      )
    )
  )
#pop-options
