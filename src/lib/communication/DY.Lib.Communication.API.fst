module DY.Lib.Communication.API

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed

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

[@@with_bytes bytes]
type communication_message_sign = {
  sender:principal;
  receiver:principal;
  payload:bytes;
  signature:bytes;
}

%splice [ps_communication_message_sign] (gen_parser (`communication_message_sign))
%splice [ps_communication_message_sign_is_well_formed] (gen_is_well_formed_lemma (`communication_message_sign))

instance parseable_serializeable_bytes_communication_message_sign: parseable_serializeable bytes communication_message_sign
  = mk_parseable_serializeable ps_communication_message_sign

[@@with_bytes bytes]
type signature_input = 
  | Plain: msg:communication_message -> signature_input
  | Encrypted: msg:communication_message -> signature_input

#push-options "--ifuel 1 --fuel 0"
%splice [ps_signature_input] (gen_parser (`signature_input))
%splice [ps_signature_input_is_well_formed] (gen_is_well_formed_lemma (`signature_input))
#pop-options

instance parseable_serializeable_bytes_signature_input: parseable_serializeable bytes signature_input
  = mk_parseable_serializeable ps_signature_input

// Response request pairs messages
[@@with_bytes bytes]
type request_message = {
  id:bytes;
  client:principal;
  payload:bytes;
  key:bytes
}

%splice [ps_request_message] (gen_parser (`request_message))
%splice [ps_request_message_is_well_formed] (gen_is_well_formed_lemma (`request_message))

instance parseable_serializeable_bytes_request_message: parseable_serializeable bytes request_message
  = mk_parseable_serializeable ps_request_message

[@@with_bytes bytes]
type response_message = {
  id:bytes;
  payload:bytes
}

%splice [ps_response_message] (gen_parser (`response_message))
%splice [ps_response_message_is_well_formed] (gen_is_well_formed_lemma (`response_message))

instance parseable_serializeable_bytes_response_message: parseable_serializeable bytes response_message
  = mk_parseable_serializeable ps_response_message

[@@with_bytes bytes]
type response_envelope = {
  nonce:bytes;
  ciphertext:bytes
}

%splice [ps_response_envelope] (gen_parser (`response_envelope))
%splice [ps_response_envelope_is_well_formed] (gen_is_well_formed_lemma (`response_envelope))

instance parseable_serializeable_bytes_response_envelope: parseable_serializeable bytes response_envelope
  = mk_parseable_serializeable ps_response_envelope

[@@with_bytes bytes]
type authenticated_data = {
  client:principal;
  server:principal
}

%splice [ps_authenticated_data] (gen_parser (`authenticated_data))
%splice [ps_authenticated_data_is_well_formed] (gen_is_well_formed_lemma (`authenticated_data))

instance parseable_serializeable_bytes_authenticated_data: parseable_serializeable bytes authenticated_data
  = mk_parseable_serializeable ps_authenticated_data


(*** States ***)

[@@with_bytes bytes]
type client_send_request = {
  id:bytes;
  server:principal;
  payload:bytes;
  key:bytes
}

%splice [ps_client_send_request] (gen_parser (`client_send_request))
%splice [ps_client_send_request_is_well_formed] (gen_is_well_formed_lemma (`client_send_request))

[@@with_bytes bytes]
type server_receive_request = {
  id:bytes;
  client:principal;
  payload:bytes;
  key:bytes
}

%splice [ps_server_receive_request] (gen_parser (`server_receive_request))
%splice [ps_server_receive_request_is_well_formed] (gen_is_well_formed_lemma (`server_receive_request))

[@@with_bytes bytes]
type client_receive_response = {
  id:bytes;
  server:principal;
  payload:bytes;
  key:bytes
}

%splice [ps_client_receive_response] (gen_parser (`client_receive_response))
%splice [ps_client_receive_response_is_well_formed] (gen_is_well_formed_lemma (`client_receive_response))

[@@with_bytes bytes]
type communication_states =
  | ClientSendRequest: client_send_request -> communication_states
  | ServerReceiveRequest: server_receive_request -> communication_states
  | ClientReceiveResponse: client_receive_response -> communication_states

#push-options "--ifuel 1"
%splice [ps_communication_states] (gen_parser (`communication_states))
%splice [ps_communication_states_is_well_formed] (gen_is_well_formed_lemma (`communication_states))
#pop-options

instance parseable_serializeable_bytes_communication_states: parseable_serializeable bytes communication_states
  = mk_parseable_serializeable ps_communication_states

instance local_state_communication_layer_session: local_state communication_states = {
  tag = "DY.Lib.Communication.State";
  format = parseable_serializeable_bytes_communication_states;
}


(*** Events ***)

[@@with_bytes bytes]
type communication_event =
  | CommConfSendMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommConfReceiveMsg: receiver:principal -> payload:bytes -> communication_event
  | CommAuthSendMsg: sender:principal -> payload:bytes -> communication_event
  | CommAuthReceiveMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommConfAuthSendMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommConfAuthReceiveMsg: sender:principal -> receiver:principal -> payload:bytes -> communication_event
  | CommClientSendRequest: client:principal -> server:principal -> id:bytes -> payload:bytes -> communication_event
  | CommServerReceiveRequest: server:principal -> id:bytes -> payload:bytes -> communication_event
  | CommServerSendResponse: server:principal -> id:bytes -> payload:bytes -> communication_event
  | CommClientReceiveResponse: client:principal -> server:principal -> id:bytes -> payload:bytes -> key:bytes -> communication_event

#push-options "--ifuel 1 --fuel 0"
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

val comm_layer_aead_tag: string
let comm_layer_aead_tag = "DY.Lib.Communication.Aead.Key"

val comm_layer_sign_tag: string
let comm_layer_sign_tag = "DY.Lib.Communication.Sign.PublicKey"

type communication_keys_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

val comm_label: principal -> principal -> label
let comm_label sender receiver = join (principal_label sender) (principal_label receiver)


(*** Communication Layer ***)

(**** Confidential Send and Receive Functions ****)

val encrypt_message: bytes -> bytes -> bytes -> bytes
let encrypt_message pk_receiver nonce payload =
  pk_enc pk_receiver nonce payload

val send_confidential:
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_confidential comm_keys_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender comm_keys_ids.pki (LongTermPkEncKey comm_layer_pkenc_tag) receiver in
  let* nonce = mk_rand PkNonce (long_term_key_label sender) 32 in
  trigger_event sender (CommConfSendMsg sender receiver payload);*
  let msg_encrypted = encrypt_message pk_receiver nonce payload in
  let* msg_id = send_msg msg_encrypted in  
  return (Some msg_id)


val decrypt_message: bytes -> bytes -> option bytes
let decrypt_message sk_receiver msg_encrypted =
  pk_dec sk_receiver msg_encrypted

val receive_confidential:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option bytes)
let receive_confidential comm_keys_ids receiver msg_id =
  let*? sk_receiver = get_private_key receiver comm_keys_ids.private_keys (LongTermPkEncKey comm_layer_pkenc_tag) in
  let*? msg_encrypted = recv_msg msg_id in
  let*? payload = return (decrypt_message sk_receiver msg_encrypted) in
  trigger_event receiver (CommConfReceiveMsg receiver payload);*
  return (Some payload)


(**** Authenticated Send and Receive Functions ****)

val sign_message: principal -> principal -> bytes -> bool -> bytes -> bytes -> bytes
let sign_message sender receiver payload is_encrypted sk nonce =
  if is_encrypted then (
    let sig_input = Encrypted {sender; receiver; payload} in
    let sig_input_bytes = serialize signature_input sig_input in
    let signature = sign sk nonce sig_input_bytes in
    let msg_signed = {sender; receiver; payload; signature} in
    serialize communication_message_sign msg_signed
  ) else (
    let sig_input = Plain {sender; receiver; payload} in
    let sig_input_bytes = serialize signature_input sig_input in
    let signature = sign sk nonce sig_input_bytes in
    let msg_signed = {sender; receiver; payload; signature} in
    serialize communication_message_sign msg_signed
  )

val send_authenticated:
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_authenticated comm_keys_ids sender receiver payload =
  let*? sk_sender = get_private_key sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) in
  let* nonce = mk_rand SigNonce (long_term_key_label sender) 32 in
  trigger_event sender (CommAuthSendMsg sender payload);*
  let msg_signed = sign_message sender receiver payload false sk_sender nonce in
  let* msg_id = send_msg msg_signed in
  return (Some msg_id)


val verify_message: principal -> bytes -> bool -> bytes -> option communication_message
let verify_message receiver msg_bytes is_encrypted vk_sender =
  let? msg_signed = parse communication_message_sign msg_bytes in
  if is_encrypted then (
    let sig_input = Encrypted {sender=msg_signed.sender; receiver=msg_signed.receiver; payload=msg_signed.payload} in
    let sig_input_bytes = serialize signature_input sig_input in
    guard (verify vk_sender sig_input_bytes msg_signed.signature);?
    guard (msg_signed.receiver = receiver);?
    Some ({sender=msg_signed.sender; receiver; payload=msg_signed.payload} <: communication_message)
  ) else (
    let sig_input = Plain {sender=msg_signed.sender; receiver=msg_signed.receiver; payload=msg_signed.payload} in
    let sig_input_bytes = serialize signature_input sig_input in
    guard (verify vk_sender sig_input_bytes msg_signed.signature);?
    guard (msg_signed.receiver = receiver);?
    Some ({sender=msg_signed.sender; receiver; payload=msg_signed.payload} <: communication_message)
  )

val get_sender: bytes -> option principal
let get_sender msg_bytes =
  let? msg = parse communication_message_sign msg_bytes in
  Some msg.sender

val receive_authenticated:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option communication_message)
let receive_authenticated comm_keys_ids receiver msg_id =
  let*? msg_signed_bytes = recv_msg msg_id in
  let*? sender = return (get_sender msg_signed_bytes) in
  let*? vk_sender = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) sender in
  let*? cm:communication_message = return (verify_message receiver msg_signed_bytes false vk_sender) in
  trigger_event receiver (CommAuthReceiveMsg sender receiver cm.payload);*
  return (Some cm)


(**** Confidential and Authenticates Send and Receive Functions ****)

val encrypt_and_sign_message: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes
let encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce =
  let enc_payload = encrypt_message pk_receiver enc_nonce payload in
  sign_message sender receiver enc_payload true sk_sender sign_nonce

// We do not encrypt the sender and receiver
// because, in real-world settings, they can also
// be identified by the IP addresses or
// certificates they use. Having the sender and
// receiver as plaintext allows us to reuse the
// functions to create and parse confidential and
// authenticated messages.
val send_confidential_authenticated:
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_confidential_authenticated comm_keys_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender comm_keys_ids.pki (LongTermPkEncKey comm_layer_pkenc_tag) receiver in
  let*? sk_sender = get_private_key sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) in
  let* enc_nonce = mk_rand PkNonce (long_term_key_label sender) 32 in
  let* sign_nonce = mk_rand SigNonce (long_term_key_label sender) 32 in
  trigger_event sender (CommConfSendMsg sender receiver payload);*
  trigger_event sender (CommConfAuthSendMsg sender receiver payload);*
  let msg_encrypted_signed_bytes = encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce in
  let* msg_id = send_msg msg_encrypted_signed_bytes in
  return (Some msg_id)

val verify_and_decrypt_message: principal -> bytes -> bytes -> bytes -> option communication_message
let verify_and_decrypt_message receiver msg_encrypted_signed sk_receiver vk_sender =
  let? cm:communication_message = verify_message receiver msg_encrypted_signed true vk_sender in
  let? payload = decrypt_message sk_receiver cm.payload in
  Some ({cm with payload} <: communication_message)

val receive_confidential_authenticated:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option communication_message)
let receive_confidential_authenticated comm_keys_ids receiver msg_id =
  let*? msg_encrypted_signed_bytes = recv_msg msg_id in
  let*? sender = return (get_sender msg_encrypted_signed_bytes) in
  let*? sk_receiver = get_private_key receiver comm_keys_ids.private_keys (LongTermPkEncKey comm_layer_pkenc_tag) in
  let*? vk_sender = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) sender in
  let*? cm:communication_message = return (verify_and_decrypt_message receiver msg_encrypted_signed_bytes sk_receiver vk_sender) in  
  trigger_event receiver (CommConfAuthReceiveMsg sender receiver cm.payload);*
  return (Some cm)

(**** Request Response Pairs ****)

val compute_request_message: principal -> bytes -> bytes -> bytes -> bytes
let compute_request_message client id payload key =
  let req:request_message = {client; id; payload; key} in
  serialize request_message req

val send_request:
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option (state_id & timestamp))
let send_request comm_keys_ids client server payload =
  let* key = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 in
  let* id = mk_rand NoUsage (join (principal_label client) (principal_label server)) 32 in
  
  let* sid = new_session_id client in
  set_state client sid (ClientSendRequest {id; server; payload; key} <: communication_states);*
  trigger_event client (CommClientSendRequest client server id payload);*
  
  let* req_payload = return (compute_request_message client id payload key) in
  let*? msg_id = send_confidential comm_keys_ids client server req_payload in
  return (Some (sid, msg_id))

val decode_request_message: bytes -> option request_message
let decode_request_message msg_bytes =
  parse request_message msg_bytes

val receive_request:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (state_id & bytes))
let receive_request comm_keys_ids server msg_id =
  let*? req_msg_bytes = receive_confidential comm_keys_ids server msg_id in
  let*? req_msg:request_message = return (decode_request_message req_msg_bytes) in
  let* sid = new_session_id server in
  set_state server sid (ServerReceiveRequest {id=req_msg.id; client=req_msg.client; payload=req_msg.payload; key=req_msg.key} <: communication_states);*
  trigger_event server (CommServerReceiveRequest server req_msg.id req_msg.payload);*
  return (Some (sid, req_msg.payload))

val compute_response_message: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes
let compute_response_message client server key nonce id payload =
  let resp:response_message = {id; payload} in
  let resp_bytes = serialize response_message resp in
  let ad:authenticated_data = {client; server} in
  let ad_bytes = serialize authenticated_data ad in
  let ciphertext = aead_enc key nonce resp_bytes ad_bytes in
  serialize response_envelope {nonce; ciphertext}

val send_response:
  communication_keys_sess_ids ->
  principal -> state_id -> bytes -> traceful (option timestamp)
let send_response comm_keys_ids server sid payload =
  let*? state = get_state server sid in
  guard_tr (ServerReceiveRequest? state);*?
  let ServerReceiveRequest srr = state in
  trigger_event server (CommServerSendResponse server srr.id payload);*
  let* nonce = mk_rand NoUsage public 32 in
  let resp_msg = compute_response_message srr.client server srr.key nonce srr.id payload in
  let* msg_id = send_msg resp_msg in
  return (Some msg_id)

val decode_response: principal -> principal -> bytes -> bytes -> option response_message
let decode_response client server key msg_bytes =
  let? resp_env:response_envelope = parse response_envelope msg_bytes in
  let ad:authenticated_data = {client; server} in
  let ad_bytes = serialize authenticated_data ad in
  let? resp_bytes = aead_dec key resp_env.nonce resp_env.ciphertext ad_bytes in
  parse response_message resp_bytes

val receive_response:
  communication_keys_sess_ids ->
  principal -> state_id -> timestamp ->
  traceful (option response_message)
let receive_response comm_keys_ids client sid msg_id =
  let*? state = get_state client sid in
  guard_tr (ClientSendRequest? state);*?
  let ClientSendRequest csr = state in
  let*? resp_msg_bytes = recv_msg msg_id in
  let*? resp_msg:response_message = return (decode_response client csr.server csr.key resp_msg_bytes) in
  set_state client sid (ClientReceiveResponse {id=csr.id; server=csr.server; payload=resp_msg.payload; key=csr.key} <: communication_states);*
  trigger_event client (CommClientReceiveResponse client csr.server csr.id resp_msg.payload csr.key);*
  return (Some resp_msg)


(**** Layer Initialization ****)

val initialize_communication: principal -> principal -> traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
let initialize_communication sender receiver =
  // Initialize keys for public key encryption
  let* client_global_session_priv_key_id = initialize_private_keys sender in
  generate_private_key sender client_global_session_priv_key_id (LongTermPkEncKey comm_layer_pkenc_tag);*

  let* receiver_global_session_priv_key_id = initialize_private_keys receiver in
  generate_private_key receiver receiver_global_session_priv_key_id (LongTermPkEncKey comm_layer_pkenc_tag);*

  let*? priv_key_receiver = get_private_key receiver receiver_global_session_priv_key_id (LongTermPkEncKey comm_layer_pkenc_tag) in
  let pub_key_receiver = pk priv_key_receiver in
  let* client_global_session_pub_key_id = initialize_pki sender in
  install_public_key sender client_global_session_pub_key_id (LongTermPkEncKey comm_layer_pkenc_tag) receiver pub_key_receiver;*

  let*? priv_key_client = get_private_key sender client_global_session_priv_key_id (LongTermPkEncKey comm_layer_pkenc_tag) in
  let pub_key_client = pk priv_key_client in
  let* receiver_global_session_pub_key_id = initialize_pki receiver in
  install_public_key receiver receiver_global_session_pub_key_id (LongTermPkEncKey comm_layer_pkenc_tag) sender pub_key_client;*

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
