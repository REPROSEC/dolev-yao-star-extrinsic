module DY.Lib.Communication.API

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Messages ***)

[@@with_bytes bytes]
type communication_message_base = {
  sender:principal;
  receiver:principal;  
  payload:bytes;
}

%splice [ps_communication_message_base] (gen_parser (`communication_message_base))
%splice [ps_communication_message_base_is_well_formed] (gen_is_well_formed_lemma (`communication_message_base))

[@@with_bytes bytes]
type communication_message_sign = {
  sender:principal;
  receiver:principal;  
  payload:bytes;
  signature:bytes;
}

%splice [ps_communication_message_sign] (gen_parser (`communication_message_sign))
%splice [ps_communication_message_sign_is_well_formed] (gen_is_well_formed_lemma (`communication_message_sign))

[@@with_bytes bytes]
type communication_message_concat = {
  enc_payload:bytes;
  signature:bytes;
}

%splice [ps_communication_message_concat] (gen_parser (`communication_message_concat))
%splice [ps_communication_message_concat_is_well_formed] (gen_is_well_formed_lemma (`communication_message_concat))

[@@with_bytes bytes]
type communication_message = 
  | CM: msg:communication_message_base -> communication_message
  | CMSign: msg:communication_message_sign -> communication_message
  | CMConcat: msg:communication_message_concat -> communication_message

#push-options "--ifuel 1 --fuel 0"
%splice [ps_communication_message] (gen_parser (`communication_message))
%splice [ps_communication_message_is_well_formed] (gen_is_well_formed_lemma (`communication_message))
#pop-options

instance parseable_serializeable_bytes_communication_message: parseable_serializeable bytes communication_message
  = mk_parseable_serializeable ps_communication_message

(*** Events ***)

#push-options "--ifuel 1 --fuel 0"
[@@with_bytes bytes]
type communication_event =
  | CommConfSendMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommConfReceiveMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommAuthSendMsg: sender:principal -> payload:bytes -> communication_event
  | CommAuthReceiveMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event

%splice [ps_communication_event] (gen_parser (`communication_event))
%splice [ps_communication_event_is_well_formed] (gen_is_well_formed_lemma (`communication_event))
#pop-options

instance event_communication_event: event communication_event = {
  tag = "DY.Lib.Communication.Event";
  format = mk_parseable_serializeable ps_communication_event;
}

(*** Layer Setup ***)

val comm_layer_pkenc_tag: string
let comm_layer_pkenc_tag = "DY.Lib.Communication.PkEnc.PublicKey"

val comm_layer_sign_tag: string
let comm_layer_sign_tag = "DY.Lib.Communication.Sign.PublicKey"

type communication_keys_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

(*** Communication Layer ***)

(**** Confidential Send and Receive Functions ****)

val encrypt_message: principal -> principal -> bytes -> bytes -> bytes -> bytes
let encrypt_message sender receiver payload pk nonce =
  let msg = CM {sender; receiver; payload} in
  let msg_bytes = serialize communication_message msg in
  pk_enc pk nonce msg_bytes

val send_confidential:
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_confidential comm_keys_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender comm_keys_ids.pki (PkEnc comm_layer_pkenc_tag) receiver in
  let* nonce = mk_rand PkNonce (principal_label sender) 32 in
  trigger_event sender (CommConfSendMsg sender receiver payload);*
  let msg_encrypted = encrypt_message sender receiver payload pk_receiver nonce in
  let* msg_id = send_msg msg_encrypted in  
  return (Some msg_id)


val decrypt_message: bytes -> bytes -> option communication_message_base
let decrypt_message sk_receiver msg_encrypted =
  let? msg_plain_bytes = pk_dec sk_receiver msg_encrypted in
  let? msg_plain = parse communication_message msg_plain_bytes in
  guard(CM? msg_plain);?
  Some (CM?.msg msg_plain)

val receive_confidential:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option communication_message_base)
let receive_confidential comm_keys_ids receiver msg_id =
  let*? sk_receiver = get_private_key receiver comm_keys_ids.private_keys (PkDec comm_layer_pkenc_tag) in
  let*? msg_encrypted = recv_msg msg_id in
  let*? msg_plain:communication_message_base = return (decrypt_message sk_receiver msg_encrypted) in
  trigger_event receiver (CommConfReceiveMsg msg_plain.sender receiver msg_plain.payload);*
  return (Some msg_plain)


(**** Authenticated Send and Receive Functions ****)

val sign_message: principal -> principal -> bytes -> bytes -> bytes -> bytes
let sign_message sender receiver payload sk nonce =
  let msg = CM {sender; receiver; payload} in
  let msg_bytes = serialize communication_message msg in
  let signature = sign sk nonce msg_bytes in
  let msg_signed = CMSign {sender; receiver; payload; signature} in
  serialize communication_message msg_signed

val send_authenticated:
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_authenticated comm_keys_ids sender receiver payload =
  let*? sk_sender = get_private_key sender comm_keys_ids.private_keys (Sign comm_layer_sign_tag) in
  let* nonce = mk_rand SigNonce (principal_label sender) 32 in
  trigger_event sender (CommAuthSendMsg sender payload);*
  let msg_signed = sign_message sender receiver payload sk_sender nonce in
  let* msg_id = send_msg msg_signed in
  return (Some msg_id)


val verify_message: principal -> bytes -> bytes -> option communication_message_base
let verify_message receiver msg_bytes vk_sender =
  let? cm_msg = parse communication_message msg_bytes in
  guard (CMSign? cm_msg);?
  let msg_signed = CMSign?.msg cm_msg in
  let msg = CM {sender=msg_signed.sender; receiver=msg_signed.receiver; payload=msg_signed.payload} in
  let msg_bytes = serialize communication_message (msg) in
  guard (verify vk_sender msg_bytes msg_signed.signature);?
  Some (CM?.msg msg)

val get_sender: bytes -> option principal
let get_sender msg_bytes =
  let? cm_msg = parse communication_message msg_bytes in
  guard (CMSign? cm_msg);?
  Some (CMSign?.msg cm_msg).sender

val receive_authenticated:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option communication_message_base)
let receive_authenticated comm_keys_ids receiver msg_id =
  let*? msg_signed = recv_msg msg_id in
  let*? sender = return (get_sender msg_signed) in
  let*? vk_sender = get_public_key receiver comm_keys_ids.pki (Verify comm_layer_sign_tag) sender in
  let*? msg_plain:communication_message_base = return (verify_message receiver msg_signed vk_sender) in
  trigger_event receiver (CommAuthReceiveMsg sender receiver msg_plain.payload);*
  return (Some msg_plain)

(**** Confidential and Authenticates Send and Receive Functions ****)

val encrypt_and_sign_message: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes
let encrypt_and_sign_message sender receiver payload pk sk enc_nonce sign_nonce =
  let enc_payload = encrypt_message sender receiver payload pk enc_nonce in
  let signature = sign sk sign_nonce enc_payload in
  let msg = CMConcat {enc_payload; signature} in
  serialize communication_message msg

val send_confidential_authenticated:
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_confidential_authenticated comm_keys_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender comm_keys_ids.pki (PkEnc comm_layer_pkenc_tag) receiver in
  let* enc_nonce = mk_rand PkNonce (principal_label sender) 32 in
  let*? sk_sender = get_private_key sender comm_keys_ids.private_keys (Sign comm_layer_sign_tag) in
  let* sig_nonce = mk_rand SigNonce (principal_label sender) 32 in
  trigger_event sender (CommConfSendMsg sender receiver payload);*
  trigger_event sender (CommAuthSendMsg sender payload);*
  let msg_encrypted_signed = encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sig_nonce in
  let* msg_id = send_msg msg_encrypted_signed in
  return (Some msg_id)

val verify_and_decrypt_message_part_one: bytes -> bytes -> option communication_message_base
let verify_and_decrypt_message_part_one msg_encrypted_signed sk_receiver =
  let? cm_msg = parse communication_message msg_encrypted_signed in
  guard (CMConcat? cm_msg);?
  let msg_concat = CMConcat?.msg cm_msg in
  let? msg_plain:communication_message_base = decrypt_message sk_receiver msg_concat.enc_payload in
  Some msg_plain

val verify_and_decrypt_message_part_two: principal -> bytes -> bytes -> option unit
let verify_and_decrypt_message_part_two sender msg_encrypted_signed vk_sender =
  let? cm_msg = parse communication_message msg_encrypted_signed in
  guard (CMConcat? cm_msg);?
  let msg_concat = CMConcat?.msg cm_msg in
  guard (verify vk_sender msg_concat.enc_payload msg_concat.signature);?
  Some ()

val receive_confidential_authenticated:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option communication_message_base)
let receive_confidential_authenticated comm_keys_ids receiver msg_id =
  let*? sk_receiver = get_private_key receiver comm_keys_ids.private_keys (PkDec comm_layer_pkenc_tag) in
  let*? msg_encrypted_signed = recv_msg msg_id in
  let*? msg_plain:communication_message_base = return (verify_and_decrypt_message_part_one msg_encrypted_signed sk_receiver) in
  let*? vk_sender = get_public_key receiver comm_keys_ids.pki (Verify comm_layer_sign_tag) msg_plain.sender in
  return (verify_and_decrypt_message_part_two msg_plain.sender msg_encrypted_signed vk_sender);*?  
  trigger_event receiver (CommConfReceiveMsg msg_plain.sender receiver msg_plain.payload);*
  trigger_event receiver (CommAuthReceiveMsg msg_plain.sender receiver msg_plain.payload);*
  return (Some msg_plain)


(**** Layer Initialization ****)

val initialize_communication: principal -> principal -> traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
let initialize_communication sender receiver =
  // Initialize keys for public key encryption
  let* client_global_session_priv_key_id = initialize_private_keys sender in
  generate_private_key sender client_global_session_priv_key_id (PkDec comm_layer_pkenc_tag);*

  let* receiver_global_session_priv_key_id = initialize_private_keys receiver in
  generate_private_key receiver receiver_global_session_priv_key_id (PkDec comm_layer_pkenc_tag);*

  let*? priv_key_receiver = get_private_key receiver receiver_global_session_priv_key_id (PkDec comm_layer_pkenc_tag) in
  let pub_key_receiver = pk priv_key_receiver in
  let* client_global_session_pub_key_id = initialize_pki sender in
  install_public_key sender client_global_session_pub_key_id (PkEnc comm_layer_pkenc_tag) receiver pub_key_receiver;*

  let*? priv_key_client = get_private_key sender client_global_session_priv_key_id (PkDec comm_layer_pkenc_tag) in
  let pub_key_client = pk priv_key_client in
  let* receiver_global_session_pub_key_id = initialize_pki receiver in
  install_public_key receiver receiver_global_session_pub_key_id (PkEnc comm_layer_pkenc_tag) sender pub_key_client;*

  // Initialize signing keys
  generate_private_key sender client_global_session_priv_key_id (Sign comm_layer_sign_tag);*
  generate_private_key receiver receiver_global_session_priv_key_id (Sign comm_layer_sign_tag);*

  let*? priv_key_receiver = get_private_key receiver receiver_global_session_priv_key_id (Sign comm_layer_sign_tag) in
  let pub_key_receiver = vk priv_key_receiver in
  install_public_key sender client_global_session_pub_key_id (Verify comm_layer_sign_tag) receiver pub_key_receiver;*

  let*? priv_key_client = get_private_key sender client_global_session_priv_key_id (Sign comm_layer_sign_tag) in
  let pub_key_client = vk priv_key_client in
  install_public_key receiver receiver_global_session_pub_key_id (Verify comm_layer_sign_tag) sender pub_key_client;*

  let client_comm_keys_sess_ids = {pki=client_global_session_pub_key_id; private_keys=client_global_session_priv_key_id} in
  let receiver_comm_keys_sess_ids = {pki=receiver_global_session_pub_key_id; private_keys=receiver_global_session_priv_key_id} in
  return (Some (client_comm_keys_sess_ids, receiver_comm_keys_sess_ids))
