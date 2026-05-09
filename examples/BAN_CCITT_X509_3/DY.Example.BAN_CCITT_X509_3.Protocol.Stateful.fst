module DY.Example.BAN_CCITT_X509_3.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.BAN_CCITT_X509_3.Protocol.Total

(*** Definition of state ***)

[@@ with_bytes bytes]
type ban_ccitt_session =
  | InitiatorSentMsg1: bob:principal -> n_a:bytes -> x_a:bytes -> y_a:bytes -> ban_ccitt_session
  | ResponderSentMsg2: alice:principal -> n_b:bytes -> x_b:bytes -> y_b:bytes -> n_a:bytes -> ban_ccitt_session
  | InitiatorSentMsg3: bob:principal -> n_b:bytes -> ban_ccitt_session
  | ResponderReceivedMsg3: alice:principal -> n_b:bytes -> ban_ccitt_session

%splice [ps_ban_ccitt_session] (gen_parser (`ban_ccitt_session))
%splice [ps_ban_ccitt_session_is_well_formed] (gen_is_well_formed_lemma (`ban_ccitt_session))

instance ban_ccitt_session_parseable_serializeable: parseable_serializeable bytes ban_ccitt_session
 = mk_parseable_serializeable ps_ban_ccitt_session

(*** Definition of events ***)
[@@ with_bytes bytes]
type ban_ccitt_event =
  | Initiate1: alice:principal -> bob:principal -> n_a:bytes -> x_a:bytes -> y_a:bytes -> ban_ccitt_event
  | Respond1: bob:principal -> alice:principal -> n_b:bytes -> x_b:bytes -> y_b:bytes -> n_a:bytes -> ban_ccitt_event
  | Initiate2: alice:principal -> bob:principal -> n_b:bytes -> ban_ccitt_event
  | Respond2: bob:principal -> alice:principal -> n_b:bytes -> ban_ccitt_event

%splice [ps_ban_ccitt_event] (gen_parser (`ban_ccitt_event))

instance ban_ccitt_event_instance: event ban_ccitt_event = {
  tag = "BAN_CCITT.Event";
  format = mk_parseable_serializeable ps_ban_ccitt_event;
}

(*** Setup for the stateful code ***)

instance local_state_ban_ccitt_session: local_state ban_ccitt_session = {
  tag = "BAN_CCITT.Session";
  format = mk_parseable_serializeable ps_ban_ccitt_session;
}

type ban_ccitt_global_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

(*** Labels ***)

val ban_ccitt_label: principal -> principal -> label
let ban_ccitt_label p1 p2 =
  principal_label p1 `join` principal_label p2

(*** Stateful code ***)

// Alice prepares and sends message 1
[@@ "opaque_to_smt"]
val send_msg1: ban_ccitt_global_sess_ids -> principal -> principal -> bytes -> bytes -> traceful (option (state_id * nat))
let send_msg1 global_sess_id alice bob x_a y_a =
  let* alice_si = new_session_id alice in
  let* n_a = mk_rand NoUsage public 32 in
  let* pke_nonce = mk_rand PkeNonce (long_term_key_label alice) 32 in
  let* sig_nonce = mk_rand SigNonce (long_term_key_label alice) 32 in
  let*? pk_b = get_public_key alice global_sess_id.pki (LongTermPkeKey "BAN_CCITT.PkeKey") bob in
  let*? sk_a = get_private_key alice global_sess_id.private_keys (LongTermSigKey "BAN_CCITT.SigKey") in
  trigger_event alice (Initiate1 alice bob n_a x_a y_a);*
  let msg = compute_message1 alice bob pk_b n_a x_a y_a pke_nonce sig_nonce sk_a in
  let* msg_id = send_msg msg in
  set_state alice alice_si (InitiatorSentMsg1 bob n_a x_a y_a);*
  return (Some (alice_si, msg_id))

// Bob receives message 1 and sends message 2
[@@ "opaque_to_smt"]
val receive_msg1_send_msg2: ban_ccitt_global_sess_ids -> principal -> principal -> nat -> bytes -> bytes -> traceful (option (state_id * nat))
let receive_msg1_send_msg2 global_sess_id bob alice msg1_id x_b y_b =
  let*? vk_a = get_public_key bob global_sess_id.pki (LongTermSigKey "BAN_CCITT.SigKey") alice in
  let*? msg1_bytes = recv_msg msg1_id in
  let*? msg1 = return (decode_message1 msg1_bytes bob vk_a) in
  let* bob_si = new_session_id bob in
  let* n_b = mk_rand NoUsage public 32 in
  let* pke_nonce = mk_rand PkeNonce (long_term_key_label bob) 32 in
  let* sig_nonce = mk_rand SigNonce (long_term_key_label bob) 32 in
  let*? pk_a = get_public_key bob global_sess_id.pki (LongTermPkeKey "BAN_CCITT.PkeKey") alice in
  let*? sk_b = get_private_key bob global_sess_id.private_keys (LongTermSigKey "BAN_CCITT.SigKey") in
  trigger_event bob (Respond1 bob alice n_b x_b y_b msg1.m1_n_a);*
  let msg2 = compute_message2 bob alice pk_a n_b msg1.m1_n_a x_b y_b pke_nonce sig_nonce sk_b in
  let* msg2_id = send_msg msg2 in
  set_state bob bob_si (ResponderSentMsg2 alice n_b x_b y_b msg1.m1_n_a);*
  return (Some (bob_si, msg2_id))

// Alice receives message 2 and sends message 3
[@@ "opaque_to_smt"]
val receive_msg2_send_msg3: ban_ccitt_global_sess_ids -> principal -> state_id -> principal -> nat -> traceful (option nat)
let receive_msg2_send_msg3 global_sess_id alice alice_si bob msg2_id =
  let*? session_state = get_state alice alice_si in
  guard_tr (InitiatorSentMsg1? session_state);*?
  let InitiatorSentMsg1 bob_id n_a x_a y_a = session_state in
  guard_tr (bob = bob_id);*?
  let*? vk_b = get_public_key alice global_sess_id.pki (LongTermSigKey "BAN_CCITT.SigKey") bob in
  let*? msg2_bytes = recv_msg msg2_id in
  let*? msg2 = return (decode_message2 msg2_bytes alice vk_b n_a) in
  let* sig_nonce = mk_rand SigNonce (long_term_key_label alice) 32 in
  let*? sk_a = get_private_key alice global_sess_id.private_keys (LongTermSigKey "BAN_CCITT.SigKey") in
  trigger_event alice (Initiate2 alice bob msg2.m2_n_b);*
  let msg3 = compute_message3 alice bob msg2.m2_n_b sig_nonce sk_a in
  let* msg3_id = send_msg msg3 in
  set_state alice alice_si (InitiatorSentMsg3 bob msg2.m2_n_b);*
  return (Some msg3_id)

// Bob receives message 3
[@@ "opaque_to_smt"]
val receive_msg3: ban_ccitt_global_sess_ids -> principal -> state_id -> principal -> nat -> traceful (option unit)
let receive_msg3 global_sess_id bob bob_si alice msg3_id =
  let*? session_state = get_state bob bob_si in
  guard_tr (ResponderSentMsg2? session_state);*?
  let ResponderSentMsg2 alice_id n_b x_b y_b n_a = session_state in
  guard_tr (alice = alice_id);*?
  let*? vk_a = get_public_key bob global_sess_id.pki (LongTermSigKey "BAN_CCITT.SigKey") alice in
  let*? msg3_bytes = recv_msg msg3_id in
  let*? msg3 = return (decode_message3 msg3_bytes bob vk_a n_b) in
  trigger_event bob (Respond2 bob alice n_b);*
  set_state bob bob_si (ResponderReceivedMsg3 alice n_b);*
  return (Some ())
