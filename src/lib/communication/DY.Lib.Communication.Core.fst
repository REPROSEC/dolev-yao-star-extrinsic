module DY.Lib.Communication.Core

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed

open DY.Lib.Communication.Data

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"


(*** Layer Setup ***)

class comm_layer_core_tag = {
  tag: string;
}

val comm_layer_pkenc_tag: {|comm_layer_core_tag|} -> string
let comm_layer_pkenc_tag #tag = tag.tag ^ ".PkEnc.PublicKey"

val comm_layer_sign_tag: {|comm_layer_core_tag|} -> string
let comm_layer_sign_tag #tag = tag.tag ^ ".Sign.PublicKey"

type communication_keys_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

val comm_label: principal -> principal -> label
let comm_label sender receiver = join (principal_label sender) (principal_label receiver)


(*** Events ***)

[@@with_bytes bytes]
type communication_event =
  | CommConfSendMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommConfReceiveMsg: receiver:principal -> payload:bytes -> communication_event
  | CommAuthSendMsg: sender:principal -> payload:bytes -> communication_event
  | CommAuthReceiveMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommConfAuthSendMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommConfAuthReceiveMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  

#push-options "--ifuel 1 --fuel 0"
%splice [ps_communication_event] (gen_parser (`communication_event))
%splice [ps_communication_event_is_well_formed] (gen_is_well_formed_lemma (`communication_event))
#pop-options

instance event_communication_event {|t:comm_layer_core_tag|}: event communication_event = {
  tag = t.tag;
  format = mk_parseable_serializeable ps_communication_event;
}


(*** Communication Layer ***)

(**** Confidential Send and Receive Functions ****)

[@@ "opaque_to_smt"]
val encrypt_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  bytes -> bytes -> a -> bytes
let encrypt_message #a pk_receiver nonce payload =
  pke_enc pk_receiver nonce (serialize a payload)

[@@ "opaque_to_smt"]
val send_confidential:
  {|comm_layer_core_tag|} ->
  #a:Type0 -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option timestamp)
let send_confidential #tag #a comm_keys_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender comm_keys_ids.pki (LongTermPkeKey comm_layer_pkenc_tag) receiver in
  let* nonce = mk_rand PkeNonce (long_term_key_label sender) 32 in
  trigger_event sender (CommConfSendMsg sender receiver (serialize a payload));*
  let msg_encrypted = encrypt_message pk_receiver nonce payload in
  let* msg_id = send_msg msg_encrypted in
  return (Some msg_id)

[@@ "opaque_to_smt"]
val decrypt_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  bytes -> bytes -> option a
let decrypt_message #a sk_receiver msg_encrypted =
  let? plaintext = pke_dec sk_receiver msg_encrypted in
  parse #bytes a plaintext

[@@ "opaque_to_smt"]
val receive_confidential:
  {|comm_layer_core_tag|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option a)
let receive_confidential #tag #a comm_keys_ids receiver msg_id =
  let*? sk_receiver = get_private_key receiver comm_keys_ids.private_keys (LongTermPkeKey comm_layer_pkenc_tag) in
  let*? msg_encrypted = recv_msg msg_id in
  let*? payload = return (decrypt_message #a sk_receiver msg_encrypted) in
  trigger_event receiver (CommConfReceiveMsg receiver (serialize a payload));*
  return (Some payload)


(**** Authenticated Send and Receive Functions ****)

#push-options "--ifuel 1"
[@@ "opaque_to_smt"]
val sign_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> principal -> a -> option bytes -> bytes -> bytes -> bytes
let sign_message #a sender receiver payload pk_receiver sk nonce =
  let payload_bytes = serialize a payload in
  let sig_input = (
    match pk_receiver with
    | None -> Plain sender receiver payload_bytes
    | Some pk -> Encrypted sender receiver payload_bytes pk
  ) in
  let sig_input_bytes = serialize signature_input sig_input in
  let signature = sign sk nonce sig_input_bytes in
  let signed_msg = SigMessage {msg=sig_input_bytes; signature} in
  serialize com_message_t signed_msg
#pop-options

[@@ "opaque_to_smt"]
val send_authenticated:
  {|comm_layer_core_tag|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option timestamp)
let send_authenticated #tag #a comm_keys_ids sender receiver payload =
  let*? sk_sender = get_private_key sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) in
  let* nonce = mk_rand SigNonce (long_term_key_label sender) 32 in
  let payload_bytes = serialize a payload in
  trigger_event sender (CommAuthSendMsg sender payload_bytes);*
  let msg_signed = sign_message sender receiver payload None sk_sender nonce in
  let* msg_id = send_msg msg_signed in
  return (Some msg_id)

#push-options "--ifuel 1 --fuel 0"
//[@@ "opaque_to_smt"]
val verify_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> bytes -> option bytes -> bytes -> option (communication_message a)
let verify_message #a receiver sign_msg_bytes sk_receiver_opt vk_sender =
  let? msg_sign_t = parse com_message_t sign_msg_bytes in
  guard (SigMessage? msg_sign_t);?
  let SigMessage msg_sign = msg_sign_t in
  let? sign_input = parse signature_input msg_sign.msg in
  guard (verify vk_sender msg_sign.msg msg_sign.signature);?
  let? (pk_receiver_opt, cm) = match sign_input with
    | Plain sender receiver payload_bytes -> (
      let? payload = parse a payload_bytes in
      Some (None, {sender; receiver; payload})
    )
    | Encrypted sender receiver payload_bytes pk_receiver -> (
      let? payload = parse a payload_bytes in
      Some (Some pk_receiver, {sender; receiver; payload})
    )
  in
  guard (cm.receiver = receiver);?
  guard (pk_receiver_opt = FStar.Option.mapTot pk sk_receiver_opt);?
  Some cm

val get_sender: bytes -> option principal
let get_sender sign_msg_bytes =
  let? msg_sign_t = parse com_message_t sign_msg_bytes in
  guard (SigMessage? msg_sign_t);?
  let SigMessage msg_sign = msg_sign_t in
  let? sign_input = parse signature_input msg_sign.msg in
  match sign_input with
  | Plain sender receiver payload_bytes -> Some sender
  | Encrypted sender receiver payload_bytes pk_receiver -> Some sender
#pop-options

[@@ "opaque_to_smt"]
val receive_authenticated:
  {|comm_layer_core_tag|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (communication_message a))
let receive_authenticated #tag #a comm_keys_ids receiver msg_id =
  let*? msg_signed_bytes = recv_msg msg_id in
  let*? sender = return (get_sender msg_signed_bytes) in
  let*? vk_sender = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) sender in
  let*? cm:communication_message a = return (verify_message receiver msg_signed_bytes None vk_sender) in
  trigger_event receiver (CommAuthReceiveMsg sender receiver (serialize a cm.payload));*
  return (Some cm)


(**** Confidential and Authenticates Send and Receive Functions ****)

[@@ "opaque_to_smt"]
val encrypt_and_sign_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> principal -> a -> bytes -> bytes -> bytes -> bytes -> bytes
let encrypt_and_sign_message #a sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce =
  let enc_payload = encrypt_message #a pk_receiver enc_nonce payload in
  sign_message #com_send_byte sender receiver {b=enc_payload} (Some pk_receiver) sk_sender sign_nonce

// We do not encrypt the sender and receiver because, in real-world settings,
// they can also be identified by the IP addresses or certificates they use.
// Having the sender and receiver as plaintext allows us to reuse the functions
// to create and parse confidential and authenticated messages.
[@@ "opaque_to_smt"]
val send_confidential_authenticated:
  {|comm_layer_core_tag|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option timestamp)
let send_confidential_authenticated #tag #a comm_keys_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender comm_keys_ids.pki (LongTermPkeKey comm_layer_pkenc_tag) receiver in
  let*? sk_sender = get_private_key sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) in
  let* enc_nonce = mk_rand PkeNonce (long_term_key_label sender) 32 in
  let* sign_nonce = mk_rand SigNonce (long_term_key_label sender) 32 in
  trigger_event sender (CommConfSendMsg sender receiver (serialize a payload));*
  trigger_event sender (CommConfAuthSendMsg sender receiver (serialize a payload));*
  let msg_encrypted_signed_bytes = encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce in
  let* msg_id = send_msg msg_encrypted_signed_bytes in
  return (Some msg_id)

[@@ "opaque_to_smt"]
val verify_and_decrypt_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> bytes -> bytes -> bytes -> option (communication_message a)
let verify_and_decrypt_message #a #ps receiver sk_receiver vk_sender msg_encrypted_signed =
  let? cm:communication_message com_send_byte = verify_message #com_send_byte receiver msg_encrypted_signed (Some sk_receiver) vk_sender in
  let? payload:a = decrypt_message #a sk_receiver cm.payload.b in
  Some {sender=cm.sender; receiver=cm.receiver; payload}

[@@ "opaque_to_smt"]
val receive_confidential_authenticated:
  {|comm_layer_core_tag|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (communication_message a))
let receive_confidential_authenticated #tag #a comm_keys_ids receiver msg_id =
  let*? msg_encrypted_signed = recv_msg msg_id in
  let*? sk_receiver = get_private_key receiver comm_keys_ids.private_keys (LongTermPkeKey comm_layer_pkenc_tag) in
  let*? sender = return (get_sender msg_encrypted_signed) in
  let*? vk_sender = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) sender in 
  let*? cm:communication_message a = return (verify_and_decrypt_message #a receiver sk_receiver vk_sender msg_encrypted_signed) in 
  trigger_event receiver (CommConfAuthReceiveMsg sender receiver (serialize a cm.payload));*
  return (Some cm)


(**** Layer Initialization ****)

[@@ "opaque_to_smt"]
val initialize_communication: {|comm_layer_core_tag|} -> principal -> principal -> traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
let initialize_communication #tag sender receiver =
  // Initialize keys for public key encryption
  let* client_global_session_priv_key_id = initialize_private_keys sender in
  generate_private_key sender client_global_session_priv_key_id (LongTermPkeKey comm_layer_pkenc_tag);*

  let* receiver_global_session_priv_key_id = initialize_private_keys receiver in
  generate_private_key receiver receiver_global_session_priv_key_id (LongTermPkeKey comm_layer_pkenc_tag);*

  let*? priv_key_receiver = get_private_key receiver receiver_global_session_priv_key_id (LongTermPkeKey comm_layer_pkenc_tag) in
  let pub_key_receiver = pk priv_key_receiver in
  let* client_global_session_pub_key_id = initialize_pki sender in
  install_public_key sender client_global_session_pub_key_id (LongTermPkeKey comm_layer_pkenc_tag) receiver pub_key_receiver;*

  let*? priv_key_client = get_private_key sender client_global_session_priv_key_id (LongTermPkeKey comm_layer_pkenc_tag) in
  let pub_key_client = pk priv_key_client in
  let* receiver_global_session_pub_key_id = initialize_pki receiver in
  install_public_key receiver receiver_global_session_pub_key_id (LongTermPkeKey comm_layer_pkenc_tag) sender pub_key_client;*

  // Initialize signing keys
  generate_private_key sender client_global_session_priv_key_id (LongTermSigKey comm_layer_sign_tag);*
  generate_private_key receiver receiver_global_session_priv_key_id (LongTermSigKey comm_layer_sign_tag);*

  let*? priv_key_receiver = get_private_key receiver receiver_global_session_priv_key_id (LongTermSigKey comm_layer_sign_tag) in
  let pub_key_receiver = vk priv_key_receiver in
  install_public_key sender client_global_session_pub_key_id (LongTermSigKey comm_layer_sign_tag) receiver pub_key_receiver;*

  let*? priv_key_client = get_private_key sender client_global_session_priv_key_id (LongTermSigKey comm_layer_sign_tag) in
  let pub_key_client = vk priv_key_client in
  install_public_key receiver receiver_global_session_pub_key_id (LongTermSigKey comm_layer_sign_tag) sender pub_key_client;*

  let client_comm_keys_sess_ids = {pki=client_global_session_pub_key_id; private_keys=client_global_session_priv_key_id} in
  let receiver_comm_keys_sess_ids = {pki=receiver_global_session_pub_key_id; private_keys=receiver_global_session_priv_key_id} in
  return (Some (client_comm_keys_sess_ids, receiver_comm_keys_sess_ids))
