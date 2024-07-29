module DY.Lib.Communication.API

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Messages ***)

[@@with_bytes bytes]
type communication_message = {
  sender:principal;
  receiver:principal;  
  payload:bytes;
}

%splice [ps_communication_message] (gen_parser (`communication_message))
%splice [ps_communication_message_is_well_formed] (gen_is_well_formed_lemma (`communication_message))

instance parseable_serializeable_bytes_communication_message: parseable_serializeable bytes communication_message
  = mk_parseable_serializeable ps_communication_message

(*** Events ***)

#push-options "--ifuel 1 --fuel 0"
[@@with_bytes bytes]
type communication_event =
  | CommunicationLayerSendMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommunicationLayerReceiveMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event

%splice [ps_communication_event] (gen_parser (`communication_event))
%splice [ps_communication_event_is_well_formed] (gen_is_well_formed_lemma (`communication_event))


instance event_communication_event: event communication_event = {
  tag = "DY.Lib.Communication.Event";
  format = mk_parseable_serializeable ps_communication_event;
}

(*** Layer Setup ***)

val comm_layer_tag: string
let comm_layer_tag = "DY.Lib.Communication.PublicKey"

(*** Communication Layer ***)

(**** Layer Initialization ****)

type communication_keys_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

val initialize_communication: principal -> principal -> traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
let initialize_communication sender receiver =
  let* client_global_session_priv_key_id = initialize_private_keys sender in
  generate_private_key sender client_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey");*

  let* receiver_global_session_priv_key_id = initialize_private_keys receiver in
  generate_private_key receiver receiver_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey");*

  let*? priv_key_receiver = get_private_key receiver receiver_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey") in
  let pub_key_receiver = pk priv_key_receiver in
  let* client_global_session_pub_key_id = initialize_pki sender in
  install_public_key sender client_global_session_pub_key_id (PkEnc "DY.Lib.Communication.PublicKey") receiver pub_key_receiver;*

  let*? priv_key_client = get_private_key sender client_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey") in
  let pub_key_client = pk priv_key_client in
  let* receiver_global_session_pub_key_id = initialize_pki receiver in
  install_public_key receiver receiver_global_session_pub_key_id (PkEnc "DY.Lib.Communication.PublicKey") sender pub_key_client;*

  let client_comm_keys_sess_ids = {pki=client_global_session_pub_key_id; private_keys=client_global_session_priv_key_id} in
  let receiver_comm_keys_sess_ids = {pki=receiver_global_session_pub_key_id; private_keys=receiver_global_session_priv_key_id} in
  return (Some (client_comm_keys_sess_ids, receiver_comm_keys_sess_ids))


(**** Confidential Send and Receive Functions ****)

val encrypt_message: principal -> principal -> bytes -> bytes -> bytes -> bytes
let encrypt_message sender receiver payload pk nonce =
  let msg = {sender; receiver; payload} in
  let msg_bytes = serialize communication_message msg in
  pk_enc pk nonce msg_bytes

val send_confidential: 
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_confidential keys_sess_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender keys_sess_ids.pki (PkEnc "DY.Lib.Communication.PublicKey") receiver in
  let* nonce = mk_rand PkNonce (principal_label sender) 32 in
  let msg_encrypted = encrypt_message sender receiver payload pk_receiver nonce in
  let* msg_id = send_msg msg_encrypted in  
  return (Some msg_id)


val decrypt_message: bytes -> bytes -> option communication_message
let decrypt_message sk_receiver msg_encrypted =
  let? msg_plain_bytes = pk_dec sk_receiver msg_encrypted in
  let? msg_plain = parse communication_message msg_plain_bytes in
  Some msg_plain

val receive_confidential:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option communication_message)
let receive_confidential keys_sess_ids receiver msg_id =
  let*? sk_receiver = get_private_key receiver keys_sess_ids.private_keys (PkDec "DY.Lib.Communication.PublicKey") in
  let*? msg_encrypted = recv_msg msg_id in
  let*? msg_plain:communication_message = return (decrypt_message sk_receiver msg_encrypted) in
  return (Some msg_plain)


(**** Confidential and Authenticated Send and Receive Functions ****)