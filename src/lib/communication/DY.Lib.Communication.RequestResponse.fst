module DY.Lib.Communication.RequestResponse

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed

open DY.Lib.Communication.Core

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Messages ***)

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


[@@with_bytes bytes]
type request_meta_data = {
  id:bytes;
  key:bytes
}


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
  tag = "DY.Lib.Communication.State.RequestResponse";
  format = parseable_serializeable_bytes_communication_states;
}

[@@with_bytes bytes]
type communication_reqres_event =
  | CommClientSendRequest: client:principal -> server:principal -> id:bytes -> payload:bytes -> key:bytes -> communication_reqres_event
  | CommServerReceiveRequest: client:principal -> server:principal -> id:bytes -> payload:bytes -> key:bytes -> communication_reqres_event
  | CommServerSendResponse: client:principal -> server:principal -> id:bytes -> payload:bytes -> communication_reqres_event
  | CommClientReceiveResponse: client:principal -> server:principal -> id:bytes -> payload:bytes -> key:bytes -> communication_reqres_event

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

(*** API ***)

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
  trigger_event client (CommClientSendRequest client server id payload key);*
  
  let* req_payload = return (compute_request_message client id payload key) in
  let*? msg_id = send_confidential comm_keys_ids client server req_payload in
  return (Some (sid, msg_id))

val decode_request_message: bytes -> option request_message
let decode_request_message msg_bytes =
  parse request_message msg_bytes

val receive_request:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (state_id & bytes & (FStar.Ghost.erased principal) & (FStar.Ghost.erased bytes) & (FStar.Ghost.erased bytes)))
let receive_request comm_keys_ids server msg_id =
  let*? req_msg_bytes = receive_confidential comm_keys_ids server msg_id in
  let*? req_msg:request_message = return (decode_request_message req_msg_bytes) in  
  trigger_event server (CommServerReceiveRequest req_msg.client server req_msg.id req_msg.payload req_msg.key);*
  let* sid = new_session_id server in
  set_state server sid (ServerReceiveRequest {id=req_msg.id; client=req_msg.client; payload=req_msg.payload; key=req_msg.key} <: communication_states);*
  let* tr = get_trace in
  return (Some (sid, req_msg.payload, FStar.Ghost.hide req_msg.client, FStar.Ghost.hide req_msg.id, FStar.Ghost.hide req_msg.key))

val mk_comm_layer_response_nonce: principal -> state_id -> usage -> traceful (option bytes)
let mk_comm_layer_response_nonce server sid usg =
  let*? state = get_state server sid in
  guard_tr (ServerReceiveRequest? state);*?
  let ServerReceiveRequest srr = state in
  let* tr = get_trace in
  let* nonce = mk_rand usg (get_label #default_crypto_usages tr srr.key) 32 in
  return (Some nonce)

val compute_response_message: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes
let compute_response_message client server key nonce id payload =
  let res:response_message = {id; payload} in
  let res_bytes = serialize response_message res in
  let ad:authenticated_data = {client; server} in
  let ad_bytes = serialize authenticated_data ad in
  let ciphertext = aead_enc key nonce res_bytes ad_bytes in
  serialize response_envelope {nonce; ciphertext}

val send_response:
  communication_keys_sess_ids ->
  principal -> state_id -> bytes -> traceful (option timestamp)
let send_response comm_keys_ids server sid payload =
  let*? state = get_state server sid in
  guard_tr (ServerReceiveRequest? state);*?
  let ServerReceiveRequest srr = state in
  trigger_event server (CommServerSendResponse srr.client server srr.id payload);*
  let* nonce = mk_rand NoUsage public 32 in
  let resp_msg = compute_response_message srr.client server srr.key nonce srr.id payload in
  let* msg_id = send_msg resp_msg in
  return (Some msg_id)

val decode_response_message: principal -> principal -> bytes -> bytes -> bytes -> option bytes
let decode_response_message client server key id msg_bytes =
  let? resp_env:response_envelope = parse response_envelope msg_bytes in
  let ad:authenticated_data = {client; server} in
  let ad_bytes = serialize authenticated_data ad in
  let? resp_bytes = aead_dec key resp_env.nonce resp_env.ciphertext ad_bytes in
  let? resp = parse response_message resp_bytes in
  guard (id = resp.id);?
  Some resp.payload

val receive_response:
  communication_keys_sess_ids ->
  principal -> state_id -> timestamp ->
  traceful (option bytes)
let receive_response comm_keys_ids client sid msg_id =
  let*? state = get_state client sid in
  guard_tr (ClientSendRequest? state);*?
  let ClientSendRequest csr = state in
  let*? resp_msg_bytes = recv_msg msg_id in
  let*? payload = return (decode_response_message client csr.server csr.key csr.id resp_msg_bytes) in
  set_state client sid (ClientReceiveResponse {id=csr.id; server=csr.server; payload; key=csr.key} <: communication_states);*
  trigger_event client (CommClientReceiveResponse client csr.server csr.id payload csr.key);*
  return (Some payload)
