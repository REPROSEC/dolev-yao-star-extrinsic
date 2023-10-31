module DY.Example.NSL.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total

[@@ with_bytes bytes]
type nsl_session =
  | InitiatorSentMsg1: b:principal -> n_a:bytes -> nsl_session
  | ResponderSentMsg2: a:principal -> n_a:bytes -> n_b:bytes -> nsl_session
  | InitiatorSentMsg3: b:principal -> n_a:bytes -> n_b:bytes -> nsl_session
  | ResponderReceivedMsg3: a:principal -> n_a:bytes -> n_b:bytes -> nsl_session

%splice [ps_nsl_session] (gen_parser (`nsl_session))
%splice [ps_nsl_session_is_well_formed] (gen_is_well_formed_lemma (`nsl_session))

instance nsl_session_parseable_serializeable: parseable_serializeable bytes nsl_session
 = mk_parseable_serializeable ps_nsl_session

val nsl_session_label: string
let nsl_session_label = "NSL.Session"

[@@ with_bytes bytes]
type nsl_event =
  | Initiate1: a:principal -> b:principal -> n_a:bytes -> nsl_event
  | Respond1: a:principal -> b:principal -> n_a:bytes -> n_b:bytes -> nsl_event
  | Initiate2: a:principal -> b:principal -> n_a:bytes -> n_b:bytes -> nsl_event
  | Respond2: a:principal -> b:principal -> n_a:bytes -> n_b:bytes -> nsl_event

%splice [ps_nsl_event] (gen_parser (`nsl_event))
%splice [ps_nsl_event_is_well_formed] (gen_is_well_formed_lemma (`nsl_event))

instance nsl_event_parseable_serializeable: parseable_serializeable bytes nsl_event
 = mk_parseable_serializeable ps_nsl_event

val nsl_event_label: string
let nsl_event_label = "NSL.Event"

type nsl_global_sess_ids = {
  pki: nat;
  private_keys: nat;
}

val prepare_msg1: principal -> principal -> crypto nat
let prepare_msg1 alice bob =
  let* n_a = mk_rand Unknown (join (principal_label alice) (principal_label bob)) 32 in
  trigger_event alice nsl_event_label (serialize nsl_event (Initiate1 alice bob n_a));*
  let* sess_id = new_session_id alice in
  set_typed_state nsl_session_label alice sess_id (InitiatorSentMsg1 bob n_a <: nsl_session);*
  return sess_id

val send_msg1: nsl_global_sess_ids -> principal -> nat -> crypto (option nat)
let send_msg1 global_sess_id alice sess_id =
  let*? st: nsl_session = get_typed_state nsl_session_label alice sess_id in
  match st with
  | InitiatorSentMsg1 bob n_a -> (
    let*? pk_b = get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob in
    let* nonce = mk_rand Unknown (principal_label alice) 32 in
    let msg = compute_message1 alice bob pk_b n_a nonce in
    let* msg_id = send_msg msg in
    return (Some msg_id)
  )
  | _ -> return None

val prepare_msg2: nsl_global_sess_ids -> principal -> nat -> crypto (option nat)
let prepare_msg2 global_sess_id bob msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_b = get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? msg1: message1 = return (decode_message1 bob msg sk_b) in
  let* n_b = mk_rand Unknown (join (principal_label msg1.alice) (principal_label bob)) 32 in
  trigger_event bob nsl_event_label (serialize nsl_event (Respond1 msg1.alice bob msg1.n_a n_b));*
  let* sess_id = new_session_id bob in
  set_typed_state nsl_session_label bob sess_id (ResponderSentMsg2 msg1.alice msg1.n_a n_b <: nsl_session);*
  return (Some sess_id)

val send_msg2: nsl_global_sess_ids -> principal -> nat -> crypto (option nat)
let send_msg2 global_sess_id bob sess_id =
  let*? st: nsl_session = get_typed_state nsl_session_label bob sess_id in
  match st with
  | ResponderSentMsg2 alice n_a n_b -> (
    let*? pk_a = get_public_key bob global_sess_id.pki (PkEnc "NSL.PublicKey") alice in
    let* nonce = mk_rand Unknown (principal_label bob) 32 in
    let msg = compute_message2 bob {n_a; alice;} pk_a n_b nonce in
    let* msg_id = send_msg msg in
    return (Some msg_id)
  )
  | _ -> return None

val prepare_msg3: nsl_global_sess_ids -> principal -> nat -> nat -> crypto (option unit)
let prepare_msg3 global_sess_id alice sess_id msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_a = get_private_key alice global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? st: nsl_session = get_typed_state nsl_session_label alice sess_id in
  match st with
  | InitiatorSentMsg1 bob n_a -> (
    let*? msg2: message2 = return (decode_message2 alice bob msg sk_a n_a) in
    trigger_event alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a msg2.n_b));*
    set_typed_state nsl_session_label alice sess_id (InitiatorSentMsg3 bob n_a msg2.n_b <: nsl_session);*
    return (Some ())
  )
  | _ -> return None

val send_msg3: nsl_global_sess_ids -> principal -> nat -> crypto (option nat)
let send_msg3 global_sess_id alice sess_id =
  let*? st: nsl_session = get_typed_state nsl_session_label alice sess_id in
  match st with
  | InitiatorSentMsg3 bob n_a n_b -> (
    let*? pk_b = get_public_key alice global_sess_id.pki (PkEnc "NSL.PublicKey") bob in
    let* nonce = mk_rand Unknown (principal_label alice) 32 in
    let msg = compute_message3 alice bob pk_b n_b nonce in
    let* msg_id = send_msg msg in
    return (Some msg_id)
  )
  | _ -> return None

val prepare_msg4: nsl_global_sess_ids -> principal -> nat -> nat -> crypto (option unit)
let prepare_msg4 global_sess_id bob sess_id msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_b = get_private_key bob global_sess_id.private_keys (PkDec "NSL.PublicKey") in
  let*? st: nsl_session = get_typed_state nsl_session_label bob sess_id in
  match st with
  | ResponderSentMsg2 alice n_a n_b -> (
    let*? msg3: message3 = return (decode_message3 alice bob msg sk_b n_b) in
    trigger_event bob nsl_event_label (serialize nsl_event (Respond2 alice bob n_a n_b));*
    set_typed_state nsl_session_label bob sess_id (ResponderReceivedMsg3 alice n_a n_b <: nsl_session);*
    return (Some ())
  )
  | _ -> return None
