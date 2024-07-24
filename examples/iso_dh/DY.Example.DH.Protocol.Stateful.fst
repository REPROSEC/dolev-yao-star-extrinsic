module DY.Example.DH.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total

(*** Definition of state ***)

[@@ with_bytes bytes]
type dh_session =
  | InitiatorSentMsg1: b:principal -> x:bytes -> dh_session
  | ResponderSentMsg2: a:principal -> gx:bytes -> gy:bytes -> y:bytes -> dh_session
  | InitiatorSendMsg3: b:principal -> gx:bytes -> gy:bytes -> k:bytes -> dh_session
  | ResponderReceivedMsg3: a:principal -> gx:bytes -> gy:bytes -> k:bytes -> dh_session

%splice [ps_dh_session] (gen_parser (`dh_session))
%splice [ps_dh_session_is_well_formed] (gen_is_well_formed_lemma (`dh_session))

instance dh_session_parseable_serializeable: parseable_serializeable bytes dh_session
 = mk_parseable_serializeable ps_dh_session

(*** Definition of events ***)
[@@ with_bytes bytes]
type dh_event =
  | Initiate1: a:principal -> b:principal -> x:bytes -> dh_event
  | Respond1: a:principal -> b:principal -> gx:bytes -> gy:bytes -> y:bytes -> dh_event
  | Initiate2: a:principal -> b:principal -> gx:bytes -> gy:bytes -> k:bytes -> dh_event
  | Respond2: a:principal -> b:principal -> gx:bytes -> gy:bytes -> k:bytes -> dh_event

%splice [ps_dh_event] (gen_parser (`dh_event))
%splice [ps_dh_event_is_well_formed] (gen_is_well_formed_lemma (`dh_event))

instance dh_event_instance: event dh_event = {
  tag = "DH.Event";
  format = mk_parseable_serializeable ps_dh_event;
}

(*** Setup for the stateful code ***)

instance local_state_dh_session: local_state dh_session = {
  tag = "DH.Session";
  format = mk_parseable_serializeable ps_dh_session;
}

type dh_global_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

(*** Stateful code ***)

// Alice prepares message 1
//
// This method is separated from the send_msg1 method
// to give the attacker more flexibility. With this
// separation an attacker can set a state without sending
// a message over the network.
val prepare_msg1: principal -> principal -> traceful state_id
let prepare_msg1 alice bob =
  let* alice_si = new_session_id alice in
  let* x = mk_rand (DhKey "DH.dh_key" empty) (principal_state_label alice alice_si) 32 in
  trigger_event alice (Initiate1 alice bob x);*
  set_state alice alice_si (InitiatorSentMsg1 bob x <: dh_session);*
  return alice_si

// Alice sends message 1
val send_msg1: principal -> state_id -> traceful (option nat)
let send_msg1 alice alice_si =
  let*? session_state: dh_session = get_state alice alice_si in
  match session_state with
  | InitiatorSentMsg1 bob x -> (
    let msg = compute_message1 alice x in
    let* msg_id = send_msg msg in
    return (Some msg_id)
  )
  | _ -> return None

// Bob prepares message 2
val prepare_msg2: principal -> principal -> nat -> traceful (option state_id)
let prepare_msg2 alice bob msg_id =
  let*? msg = recv_msg msg_id in
  let*? msg1: message1 = return (decode_message1 msg) in
  let* bob_si = new_session_id bob in
  let* y = mk_rand (DhKey "DH.dh_key" empty) (principal_state_label bob bob_si) 32 in
  trigger_event bob (Respond1 alice bob msg1.gx (dh_pk y) y);*
  set_state bob bob_si (ResponderSentMsg2 alice msg1.gx (dh_pk y) y <: dh_session);*
  return (Some bob_si)

// Bob sends message 2
val send_msg2: dh_global_sess_ids -> principal -> state_id -> traceful (option nat)
let send_msg2 global_sess_id bob bob_si =
  let*? session_state: dh_session = get_state bob bob_si in
  match session_state with
  | ResponderSentMsg2 alice gx gy y -> (
    let*? sk_b = get_private_key bob global_sess_id.private_keys (Sign "DH.SigningKey") in
    let* n_sig = mk_rand SigNonce (principal_label bob) 32 in
    let msg = compute_message2 alice bob gx gy sk_b n_sig in
    let* msg_id = send_msg msg in
    return (Some msg_id)
  )
  | _ -> return None

// Alice prepares message 3
//
// This function has to verify the signature from message 2
val prepare_msg3: dh_global_sess_ids -> principal -> state_id -> principal -> nat -> traceful (option unit)
let prepare_msg3 global_sess_id alice alice_si bob msg_id =
  let*? session_state: dh_session = get_state alice alice_si in
  match session_state with
  | InitiatorSentMsg1 bob x -> (
    let*? pk_b = get_public_key alice global_sess_id.pki (Verify "DH.SigningKey") bob in
    let*? msg = recv_msg msg_id in
    let*? res:verify_msg2_result = return (decode_and_verify_message2 msg alice x pk_b) in
    trigger_event alice (Initiate2 alice bob res.gx res.gy res.k);*
    set_state alice alice_si (InitiatorSendMsg3 bob res.gx res.gy res.k <: dh_session);*
    return (Some ())
  )
  | _ -> return None

// Alice send message 3
val send_msg3: dh_global_sess_ids -> principal -> principal -> state_id -> traceful (option nat)
let send_msg3 global_sess_id alice bob alice_si =
  let*? session_state: dh_session = get_state alice alice_si in
  match session_state with
  | InitiatorSendMsg3 bob gx gy x -> (
    let*? sk_a = get_private_key alice global_sess_id.private_keys (Sign "DH.SigningKey") in
    let* n_sig = mk_rand SigNonce (principal_label alice) 32 in
    let msg = compute_message3 alice bob gx gy sk_a n_sig in
    let* msg_id = send_msg msg in
    return (Some msg_id)
  )
  | _ -> return None

// Bob verifies message 3
val verify_msg3: dh_global_sess_ids -> principal -> principal -> nat -> state_id -> traceful (option unit)
let verify_msg3 global_sess_id alice bob msg_id bob_si =
  let*? session_state: dh_session = get_state bob bob_si in
  match session_state with
  | ResponderSentMsg2 alice gx gy y -> (
    let*? pk_a = get_public_key bob global_sess_id.pki (Verify "DH.SigningKey") alice in
    let*? msg = recv_msg msg_id in
    let*? res:verify_msg3_result = return (decode_and_verify_message3 msg bob gx gy y pk_a) in
    trigger_event bob (Respond2 alice bob gx gy res.k);*
    set_state bob bob_si (ResponderReceivedMsg3 alice gx gy res.k <: dh_session);*
    return (Some ())
  )
  | _ -> return None