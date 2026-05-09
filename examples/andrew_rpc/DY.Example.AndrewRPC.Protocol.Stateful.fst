module DY.Example.AndrewRPC.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.AndrewRPC.Protocol.Total

(*** Definition of state ***)

[@@ with_bytes bytes]
type andrew_rpc_session =
  | InitiatorSentMsg1: bob:principal -> n_a:bytes -> andrew_rpc_session
  | InitiatorReceivedMsg2: bob:principal -> n_a:bytes -> k_prime_ab:bytes -> andrew_rpc_session
  | ResponderReceivedMsg1: alice:principal -> n_a:bytes -> andrew_rpc_session
  | ResponderSentMsg2: alice:principal -> n_a:bytes -> k_prime_ab:bytes -> andrew_rpc_session
  | ResponderReceivedMsg3: alice:principal -> n_a:bytes -> k_prime_ab:bytes -> andrew_rpc_session

%splice [ps_andrew_rpc_session] (gen_parser (`andrew_rpc_session))
%splice [ps_andrew_rpc_session_is_well_formed] (gen_is_well_formed_lemma (`andrew_rpc_session))

instance andrew_rpc_session_parseable_serializeable: parseable_serializeable bytes andrew_rpc_session
 = mk_parseable_serializeable ps_andrew_rpc_session

(*** Definition of events ***)
[@@ with_bytes bytes]
type andrew_rpc_event =
  | Initiate1: alice:principal -> bob:principal -> n_a:bytes -> andrew_rpc_event
  | Respond1: alice:principal -> bob:principal -> n_a:bytes -> k_prime_ab:bytes -> andrew_rpc_event
  | Initiate2: alice:principal -> bob:principal -> n_a:bytes -> andrew_rpc_event
  | Respond2: alice:principal -> bob:principal -> n_a:bytes -> k_prime_ab:bytes -> andrew_rpc_event

%splice [ps_andrew_rpc_event] (gen_parser (`andrew_rpc_event))

instance andrew_rpc_event_instance: event andrew_rpc_event = {
  tag = "AndrewRPC.Event";
  format = mk_parseable_serializeable ps_andrew_rpc_event;
}

(*** Setup for the stateful code ***)

instance local_state_andrew_rpc_session: local_state andrew_rpc_session = {
  tag = "AndrewRPC.Session";
  format = mk_parseable_serializeable ps_andrew_rpc_session;
}

val andrew_rpc_kab_tag: string
let andrew_rpc_kab_tag = "AndrewRPC.Kab"

val andrew_rpc_k_prime_ab_tag: string
let andrew_rpc_k_prime_ab_tag = "AndrewRPC.K_prime_ab"

(*** Labels used to generate randomness ***)

val andrew_rpc_nonce_label: principal -> principal -> label
let andrew_rpc_nonce_label alice bob =
  join (principal_label alice) (principal_label bob)

val andrew_rpc_session_key_label: principal -> principal -> bytes -> label
let andrew_rpc_session_key_label alice bob n_a =
  join (principal_label alice) (principal_label bob)

(*** Stateful code ***)

// Alice initiates the protocol
[@@ "opaque_to_smt"]
val alice_send_msg1: principal -> principal -> traceful (state_id & nat)
let alice_send_msg1 alice bob =
  let* sid = new_session_id alice in
  let* n_a = mk_rand NoUsage public 32 in
  trigger_event alice (Initiate1 alice bob n_a);*
  set_state alice sid (InitiatorSentMsg1 bob n_a);*
  let msg = compute_message1 alice n_a in
  let* msg_id = send_msg msg in
  return (sid, msg_id)

// Bob receives msg1 and sends msg2
[@@ "opaque_to_smt"]
val bob_recv_msg1_send_msg2: principal -> principal -> bytes -> nat -> traceful (option (state_id & nat))
let bob_recv_msg1_send_msg2 bob alice kab msg1_id =
  let*? msg1_bytes = recv_msg msg1_id in
  let*? (alice_recv, n_a) = return (decode_message1 msg1_bytes) in
  guard_tr (alice = alice_recv);*?
  let* sid = new_session_id bob in
  let* k_prime_ab = mk_rand (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = n_a})) (andrew_rpc_session_key_label alice bob n_a) 32 in
  let* nonce = mk_rand NoUsage public 12 in
  trigger_event bob (Respond1 alice bob n_a k_prime_ab);*
  set_state bob sid (ResponderSentMsg2 alice n_a k_prime_ab);*
  let msg2 = compute_message2 kab n_a k_prime_ab nonce bob in
  let* msg2_id = send_msg msg2 in
  return (Some (sid, msg2_id))

// Alice receives msg2 and sends msg3
[@@ "opaque_to_smt"]
val alice_recv_msg2_send_msg3: principal -> principal -> state_id -> bytes -> nat -> traceful (option nat)
let alice_recv_msg2_send_msg3 alice bob sid kab msg2_id =
  let*? session = get_state alice sid in
  guard_tr (InitiatorSentMsg1? session);*?
  let InitiatorSentMsg1 bob_sess n_a = session in
  guard_tr (bob_sess = bob);*?
  let*? msg2_bytes = recv_msg msg2_id in
  let*? msg2 = return (decode_message2 kab msg2_bytes) in
  guard_tr (msg2.m2_n_a = n_a);*?
  guard_tr (msg2.m2_bob = bob);*?
  trigger_event alice (Initiate2 alice bob n_a);*
  set_state alice sid (InitiatorReceivedMsg2 bob n_a msg2.m2_k_prime_ab);*
  let* nonce3 = mk_rand NoUsage public 12 in
  let msg3 = compute_message3 msg2.m2_k_prime_ab n_a nonce3 in
  let* msg3_id = send_msg msg3 in
  return (Some msg3_id)

// Bob receives msg3 and sends msg4
[@@ "opaque_to_smt"]
val bob_recv_msg3_send_msg4: principal -> state_id -> nat -> traceful (option nat)
let bob_recv_msg3_send_msg4 bob sid msg3_id =
  let*? session = get_state bob sid in
  guard_tr (ResponderSentMsg2? session);*?
  let ResponderSentMsg2 alice n_a k_prime_ab = session in
  let*? msg3_bytes = recv_msg msg3_id in
  let*? msg3 = return (decode_message3 k_prime_ab msg3_bytes) in
  guard_tr (msg3.m3_n_a = n_a);*?
  trigger_event bob (Respond2 alice bob n_a k_prime_ab);*
  set_state bob sid (ResponderReceivedMsg3 alice n_a k_prime_ab);*
  let* n_b = mk_rand NoUsage public 32 in
  let msg4 = compute_message4 n_b in
  let* msg4_id = send_msg msg4 in
  return (Some msg4_id)
