module DY.Example.NSL.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total

/// This module implements the impure (or stateful) part of the NSL protocol.
/// This effectively connects the pure code of NSL to the outside world,
/// by handling network connections, state storage, or random generation.

(*** State type ***)

/// Type for the NSL state machine

[@@ with_bytes bytes]
type nsl_session =
  | InitiatorSendingMsg1: b:principal -> n_a:bytes -> nsl_session
  | ResponderSendingMsg2: a:principal -> n_a:bytes -> n_b:bytes -> nsl_session
  | InitiatorSendingMsg3: b:principal -> n_a:bytes -> n_b:bytes -> nsl_session
  | ResponderReceivedMsg3: a:principal -> n_a:bytes -> n_b:bytes -> nsl_session

%splice [ps_nsl_session] (gen_parser (`nsl_session))
%splice [ps_nsl_session_is_well_formed] (gen_is_well_formed_lemma (`nsl_session))

instance parseable_serializeable_bytes_nsl_session: parseable_serializeable bytes nsl_session
 = mk_parseable_serializeable ps_nsl_session

instance local_state_nsl_session: local_state nsl_session = {
  tag = "NSL.Session";
  format = parseable_serializeable_bytes_nsl_session;
}


(*** Event type ***)

/// Type for the NSL protocol events.
/// They will be used to write authentication security properties.

[@@ with_bytes bytes]
type nsl_event =
  | Responding: a:principal -> b:principal -> n_a:bytes -> n_b:bytes -> nsl_event

%splice [ps_nsl_event] (gen_parser (`nsl_event))
%splice [ps_nsl_event_is_well_formed] (gen_is_well_formed_lemma (`nsl_event))

instance event_nsl_event: event nsl_event = {
  tag = "NSL.Event";
  format = mk_parseable_serializeable ps_nsl_event;
}


(*** Stateful code ***)

type nsl_global_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

val prepare_msg1: principal -> principal -> traceful state_id
let prepare_msg1 alice bob =
  let* n_a = mk_rand NoUsage (join (principal_label alice) (principal_label bob)) 32 in
  let* sess_id = new_session_id alice in
  set_state alice sess_id (InitiatorSendingMsg1 bob n_a <: nsl_session);*
  return sess_id

val send_msg1: nsl_global_sess_ids -> principal -> state_id -> traceful (option timestamp)
let send_msg1 global_sess_id alice sess_id =
  let*? st = get_state alice sess_id in
  guard_tr (InitiatorSendingMsg1? st);*?
  let InitiatorSendingMsg1 bob n_a = st in
  let*? pk_b = get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob in
  let* nonce = mk_rand PkNonce (principal_label alice) 32 in
  let msg = compute_message1 alice bob pk_b n_a nonce in
  let* msg_id = send_msg msg in
  return (Some msg_id)

val send_msg1_: nsl_global_sess_ids -> principal -> principal -> traceful (option (timestamp & state_id))
let send_msg1_ global_sess_id alice bob =
  let* n_a = mk_rand NoUsage (join (principal_label alice) (principal_label bob)) 32 in

  let* sess_id = new_session_id alice in
  let st = InitiatorSendingMsg1 bob n_a in
  set_state alice sess_id st;*

  let*? pk_b = get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob in
  let* nonce = mk_rand PkNonce (principal_label alice) 32 in
  let msg = compute_message1 alice bob pk_b n_a nonce in
  let* msg_id = send_msg msg in
  
  return (Some (msg_id, sess_id))


val prepare_msg2: nsl_global_sess_ids -> principal -> timestamp -> traceful (option state_id)
let prepare_msg2 global_sess_id bob msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_b = get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? msg1: message1 = return (decode_message1 bob msg sk_b) in
  let* n_b = mk_rand NoUsage (join (principal_label msg1.alice) (principal_label bob)) 32 in
  trigger_event bob (Responding msg1.alice bob msg1.n_a n_b);*
  let* sess_id = new_session_id bob in
  set_state bob sess_id (ResponderSendingMsg2 msg1.alice msg1.n_a n_b <: nsl_session);*
  return (Some sess_id)

val send_msg2: nsl_global_sess_ids -> principal -> state_id -> traceful (option timestamp)
let send_msg2 global_sess_id bob sess_id =
  let*? st = get_state bob sess_id in
  guard_tr (ResponderSendingMsg2? st);*?
  let ResponderSendingMsg2 alice n_a n_b = st in
  let*? pk_a = get_public_key bob global_sess_id.pki (PkEnc "NSL.PublicKey") alice in
  let* nonce = mk_rand PkNonce (principal_label bob) 32 in
  let msg = compute_message2 bob {n_a; alice;} pk_a n_b nonce in
  let* msg_id = send_msg msg in
  return (Some msg_id)


val send_msg2_: nsl_global_sess_ids -> principal -> timestamp -> traceful (option (timestamp & state_id))
let send_msg2_ global_sess_id bob msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_b = get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? msg1: message1 = return (decode_message1 bob msg sk_b) in

  let alice = msg1.alice in
  let n_a = msg1.n_a in
  let* n_b = mk_rand NoUsage (join (principal_label alice) (principal_label bob)) 32 in
  trigger_event bob (Responding alice bob n_a n_b);*
  
  let st = ResponderSendingMsg2 alice n_a n_b in
  let* sess_id = new_session_id bob in
  set_state bob sess_id st;*
  
  let*? pk_a = get_public_key bob global_sess_id.pki (PkEnc "NSL.PublicKey") msg1.alice in
  let* nonce = mk_rand PkNonce (principal_label bob) 32 in
  let msg2 = compute_message2 bob {n_a; alice;} pk_a n_b nonce in
  let* msg_id = send_msg msg2 in

  
  return (Some (msg_id, sess_id))

val prepare_msg3: nsl_global_sess_ids -> principal -> state_id -> timestamp -> traceful (option unit)
let prepare_msg3 global_sess_id alice sess_id msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_a = get_private_key alice global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? st = get_state alice sess_id in
  guard_tr (InitiatorSendingMsg1? st);*?
  let InitiatorSendingMsg1 bob n_a = st in
  let*? msg2: message2 = return (decode_message2 alice bob msg sk_a n_a) in
  set_state alice sess_id (InitiatorSendingMsg3 bob n_a msg2.n_b <: nsl_session);*
  return (Some ())

val prepare_msg3_: nsl_global_sess_ids -> principal -> timestamp -> traceful (option state_id)
let prepare_msg3_ global_sess_id alice msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_a = get_private_key alice global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? msg2: message2 = return (decode_message2_ alice msg sk_a) in
  let p = (fun (s:nsl_session) -> 
    (InitiatorSendingMsg1? s) && 
    (InitiatorSendingMsg1?.n_a s = msg2.n_a) && 
    (InitiatorSendingMsg1?.b s = msg2.bob))  in
  let* tr = get_trace in
  let (opt_st, _) = lookup_state #nsl_session alice p tr in
  match opt_st with
  | None -> return None
  | Some (st, sid ) -> (
      let InitiatorSendingMsg1 bob n_a = st in
      set_state alice sid (InitiatorSendingMsg3 bob n_a msg2.n_b <: nsl_session);*
      return (Some sid)
  )


val send_msg3: nsl_global_sess_ids -> principal -> state_id -> traceful (option timestamp)
let send_msg3 global_sess_id alice sess_id =
  let*? st = get_state alice sess_id in
  guard_tr (InitiatorSendingMsg3? st);*?
  let InitiatorSendingMsg3 bob n_a n_b = st in
  let*? pk_b = get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob in
  let* nonce = mk_rand PkNonce (principal_label alice) 32 in
  let msg = compute_message3 alice bob pk_b n_b nonce in
  let* msg_id = send_msg msg in
  return (Some msg_id)

val send_msg3_: nsl_global_sess_ids -> principal -> timestamp -> traceful (option (timestamp & state_id))
let send_msg3_ global_sess_id alice msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_a = get_private_key alice global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? msg2: message2 = return (decode_message2_ alice msg sk_a) in
  
  let p = (fun (s:nsl_session) -> 
    (InitiatorSendingMsg1? s) && 
    (InitiatorSendingMsg1?.n_a s = msg2.n_a) && 
    (InitiatorSendingMsg1?.b s = msg2.bob))  in
  let* tr = get_trace in
  let (opt_st, _) = lookup_state #nsl_session alice p tr in
  match opt_st with
  | None -> return None
  | Some (st, sid ) -> (
      let n_b = msg2.n_b in
      let InitiatorSendingMsg1 bob n_a = st in
      let st = InitiatorSendingMsg3 bob n_a n_b in
      set_state alice sid st;*
  
  let*? pk_b = get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob in
  let* nonce = mk_rand PkNonce (principal_label alice) 32 in
  let msg3 = compute_message3 alice bob pk_b n_b nonce in
  let* msg_id = send_msg msg3 in
  return (Some (msg_id, sid))
  )

val prepare_msg4: nsl_global_sess_ids -> principal -> state_id -> timestamp -> traceful (option unit)
let prepare_msg4 global_sess_id bob sess_id msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_b = get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? st = get_state bob sess_id in
  guard_tr (ResponderSendingMsg2? st);*?
  let ResponderSendingMsg2 alice n_a n_b = st in
  let*? msg3: message3 = return (decode_message3 alice bob msg sk_b n_b) in
  set_state bob sess_id (ResponderReceivedMsg3 alice n_a n_b <: nsl_session);*
  return (Some ())

val receive_msg3: nsl_global_sess_ids -> principal -> timestamp -> traceful (option unit)
let receive_msg3 global_sess_id bob msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_b = get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") in

  let*? msg3: message3 = return (decode_message3_ msg sk_b) in
  let p = (fun (s:nsl_session) -> 
    (ResponderSendingMsg2? s) && 
    (ResponderSendingMsg2?.n_b s = msg3.n_b)) in
  let* tr = get_trace in
  let (opt_st, _) = lookup_state #nsl_session bob p tr in
  match opt_st with
  | None -> return None
  | Some (st, sid ) -> (
         let ResponderSendingMsg2 alice n_a n_b = st in
         set_state bob sid (ResponderReceivedMsg3 alice n_a n_b <: nsl_session);*
  return (Some ())
  )
