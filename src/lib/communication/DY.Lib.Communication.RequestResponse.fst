module DY.Lib.Communication.RequestResponse

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** States ***)

[@@with_bytes bytes]
type client_send_request = {
  server:principal;
  payload:bytes;
  key:bytes
}

%splice [ps_client_send_request] (gen_parser (`client_send_request))
%splice [ps_client_send_request_is_well_formed] (gen_is_well_formed_lemma (`client_send_request))

[@@with_bytes bytes]
type server_receive_request = {
  payload:bytes;
  key:bytes
}

%splice [ps_server_receive_request] (gen_parser (`server_receive_request))
%splice [ps_server_receive_request_is_well_formed] (gen_is_well_formed_lemma (`server_receive_request))

[@@with_bytes bytes]
type client_receive_response = {
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
  tag = "DY.Lib.Communication.State.RequestResponse";
  format = parseable_serializeable_bytes_communication_states;
}

[@@with_bytes bytes]
type communication_reqres_event =
  | CommClientSendRequest: client:principal -> server:principal -> payload:bytes -> key:bytes -> communication_reqres_event
  | CommServerReceiveRequest: server:principal -> payload:bytes -> key:bytes -> communication_reqres_event
  | CommServerSendResponse: server:principal -> payload:bytes -> communication_reqres_event
  | CommClientReceiveResponse: client:principal -> server:principal -> payload:bytes -> key:bytes -> communication_reqres_event

#push-options "--ifuel 1"
%splice [ps_communication_reqres_event] (gen_parser (`communication_reqres_event))
%splice [ps_communication_reqres_event_is_well_formed] (gen_is_well_formed_lemma (`communication_reqres_event))
#pop-options

instance event_communication_reqres_event: event communication_reqres_event = {
  tag = "DY.Lib.Communication.Event.RequestResponse";
  format = mk_parseable_serializeable ps_communication_reqres_event;
}

(*** Layer Setup ***)

val comm_layer_aead_tag: string
let comm_layer_aead_tag = "DY.Lib.Communication.Aead.Key"

[@@with_bytes bytes]
type comm_meta_data = {
  key:bytes;
  server:principal;
  sid:state_id;
}

%splice [ps_comm_meta_data] (gen_parser (`comm_meta_data))
%splice [ps_comm_meta_data_is_well_formed] (gen_is_well_formed_lemma (`comm_meta_data))


(*** API ***)

val send_request:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option (timestamp & comm_meta_data))
let send_request #a comm_keys_ids client server payload =
  let* key = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 in
  let payload_bytes = serialize #bytes a payload in
  let* sid = new_session_id client in
  set_state client sid (ClientSendRequest {server; payload=payload_bytes; key} <: communication_states);*
  trigger_event client (CommClientSendRequest client server payload_bytes key);*
  let req_payload:com_message_t = RequestMessage {payload=payload_bytes; key} in
  let*? msg_id = send_confidential #com_message_t comm_keys_ids client server req_payload in
  let req_meta_data = {key; server; sid} in
  return (Some (msg_id, req_meta_data))

val receive_request:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (a & comm_meta_data))
let receive_request #a comm_keys_ids server msg_id =
  let*? req_msg_t:com_message_t = receive_confidential #com_message_t comm_keys_ids server msg_id in  
  guard_tr (RequestMessage? req_msg_t);*?
  let RequestMessage req_msg = req_msg_t in
  trigger_event server (CommServerReceiveRequest server req_msg.payload req_msg.key);*
  let* sid = new_session_id server in
  set_state server sid (ServerReceiveRequest {payload=req_msg.payload; key=req_msg.key} <: communication_states);*
  let*? payload = return (parse a req_msg.payload) in
  let req_meta_data = {key=req_msg.key; server; sid} in
  return (Some (payload, req_meta_data))

val mk_comm_layer_response_nonce: comm_meta_data -> usage -> traceful (option bytes)
let mk_comm_layer_response_nonce req_meta_data usg =
  let* tr = get_trace in
  let* nonce = mk_rand usg (get_label #default_crypto_usages tr req_meta_data.key) 32 in
  return (Some nonce)

val mk_comm_layer_response_nonce_labeled: comm_meta_data -> usage -> label -> traceful (option bytes)
let mk_comm_layer_response_nonce_labeled req_meta_data usg lab =
  let* tr = get_trace in
  let lab_join = join lab (get_label #default_crypto_usages tr req_meta_data.key) in
  let* nonce = mk_rand usg lab_join 32 in
  return (Some nonce)

val compute_response_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> bytes -> bytes -> a -> bytes
let compute_response_message #a server key nonce payload =
  let res_bytes = serialize a payload in
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  let ciphertext = aead_enc key nonce res_bytes ad_bytes in
  serialize com_message_t (ResponseMessage {nonce; ciphertext})

val send_response:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> comm_meta_data -> a -> traceful (option timestamp)
let send_response #a server req_meta_data payload =
  let*? state = get_state server req_meta_data.sid in
  guard_tr (ServerReceiveRequest? state);*?
  let ServerReceiveRequest srr = state in
  guard_tr (srr.key = req_meta_data.key);*?
  trigger_event server (CommServerSendResponse server (serialize a payload));*
  let* nonce = mk_rand NoUsage public 32 in
  let resp_msg = compute_response_message server req_meta_data.key nonce payload in
  let* msg_id = send_msg resp_msg in
  return (Some msg_id)

val decode_response_message:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> bytes -> bytes -> option a
let decode_response_message #a server key msg_bytes =
  let? resp_env_t:com_message_t = parse com_message_t msg_bytes in
  guard (ResponseMessage? resp_env_t);?
  let ResponseMessage resp_env = resp_env_t in
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  let? resp_bytes = aead_dec key resp_env.nonce resp_env.ciphertext ad_bytes in
  let? resp = parse a resp_bytes in
  Some resp

val receive_response:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> comm_meta_data -> timestamp ->
  traceful (option (a & comm_meta_data))
let receive_response #a client req_meta_data msg_id =
  let*? state = get_state client req_meta_data.sid in
  guard_tr (ClientSendRequest? state);*?
  let ClientSendRequest csr = state in
  let*? resp_msg_bytes = recv_msg msg_id in
  let*? payload = return (decode_response_message #a csr.server csr.key resp_msg_bytes) in
  guard_tr (csr.server = req_meta_data.server);*?
  guard_tr (csr.key = req_meta_data.key);*?
  set_state client req_meta_data.sid (ClientReceiveResponse {server=csr.server; payload=(serialize a payload); key=csr.key} <: communication_states);*
  trigger_event client (CommClientReceiveResponse client csr.server (serialize a payload) csr.key);*
  return (Some (payload, req_meta_data))
