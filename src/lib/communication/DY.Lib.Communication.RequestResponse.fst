module DY.Lib.Communication.RequestResponse

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed
open DY.Lib.Comparse.Glue

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Layer Setup ***)

class comparse_parser_serializer (a:Type) = {
  ps_a: parser_serializer bytes a;
  ps_able: parseable_serializeable bytes a;
  [@@@FStar.Tactics.Typeclasses.no_method]
  eq_property: squash (ps_able == mk_parseable_serializeable ps_a);
}

class comm_layer_reqres_tag = {
  tag: string;
}

instance comm_layer_tag_core_reqres: comm_layer_core_tag = {
  tag = "DY.Lib.Communication.Event.RequestResponse.Core"
}

val comm_layer_aead_tag: {|comm_layer_reqres_tag|} -> string
let comm_layer_aead_tag #tag = tag.tag ^ ".Aead.Key"

[@@with_bytes bytes]
type comm_meta_data (a:Type) {|ps:comparse_parser_serializer a|} = {
  key:bytes;
  server:principal;
  sid:state_id;
  [@@@ with_parser #bytes ps.ps_a]
  request:a;
}

%splice [ps_comm_meta_data] (gen_parser (`comm_meta_data))
%splice [ps_comm_meta_data_is_well_formed] (gen_is_well_formed_lemma (`comm_meta_data))


(*** States ***)

[@@with_bytes bytes]
type client_send_request (a:Type) {|ps:comparse_parser_serializer a|} = {
  server:principal;
  [@@@ with_parser #bytes ps.ps_a]
  request:a;
  key:bytes
}

%splice [ps_client_send_request] (gen_parser (`client_send_request))
%splice [ps_client_send_request_is_well_formed] (gen_is_well_formed_lemma (`client_send_request))

[@@with_bytes bytes]
type server_receive_request (a:Type) {|ps:comparse_parser_serializer a|} = {
  [@@@ with_parser #bytes ps.ps_a]
  request:a;
  key:bytes
}

%splice [ps_server_receive_request] (gen_parser (`server_receive_request))
%splice [ps_server_receive_request_is_well_formed] (gen_is_well_formed_lemma (`server_receive_request))

[@@with_bytes bytes]
type client_receive_response (a:Type) {|ps:comparse_parser_serializer a|} = {
  server:principal;
  [@@@ with_parser #bytes ps.ps_a]
  response:a;
  key:bytes
}

%splice [ps_client_receive_response] (gen_parser (`client_receive_response))
%splice [ps_client_receive_response_is_well_formed] (gen_is_well_formed_lemma (`client_receive_response))

[@@with_bytes bytes]
type communication_states (a:Type) {|ps:comparse_parser_serializer a|} =
  | ClientSendRequest: client_send_request a -> communication_states a
  | ServerReceiveRequest: server_receive_request a -> communication_states a
  | ClientReceiveResponse: client_receive_response a -> communication_states a

#push-options "--ifuel 1"
%splice [ps_communication_states] (gen_parser (`communication_states))
%splice [ps_communication_states_is_well_formed] (gen_is_well_formed_lemma (`communication_states))
#pop-options

instance parseable_serializeable_bytes_communication_states (a:Type) {|comparse_parser_serializer a|}: parseable_serializeable bytes (communication_states a)
  = mk_parseable_serializeable (ps_communication_states a)

instance local_state_communication_layer_session {|t:comm_layer_reqres_tag|} (a:Type) {|comparse_parser_serializer a|}: local_state (communication_states a) = {
  tag = t.tag ^ ".State";
  format = parseable_serializeable_bytes_communication_states a;
}

[@@with_bytes bytes]
type communication_reqres_event =
  | CommClientSendRequest: client:principal -> server:principal -> request:bytes -> key:bytes -> communication_reqres_event
  | CommServerReceiveRequest: server:principal -> request:bytes -> key:bytes -> communication_reqres_event
  | CommServerSendResponse: server:principal -> request:bytes -> response:bytes -> communication_reqres_event
  | CommClientReceiveResponse: client:principal -> server:principal -> response:bytes -> key:bytes -> communication_reqres_event

#push-options "--ifuel 1"
%splice [ps_communication_reqres_event] (gen_parser (`communication_reqres_event))
%splice [ps_communication_reqres_event_is_well_formed] (gen_is_well_formed_lemma (`communication_reqres_event))
#pop-options

instance event_communication_reqres_event {|t:comm_layer_reqres_tag|}: event communication_reqres_event = {
  tag = t.tag ^ ".Event";
  format = mk_parseable_serializeable ps_communication_reqres_event;
}


(*** API ***)

[@@ "opaque_to_smt"]
val send_request:
  {|comm_layer_reqres_tag|} ->
  #a:Type -> {|comparse_parser_serializer a|} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option (timestamp & comm_meta_data a))
let send_request #tag #a #ps comm_keys_ids client server request =
  let* key = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 in
  let payload_bytes:bytes = serialize a #ps_able request in
  let* sid = new_session_id client in
  set_state client sid (ClientSendRequest {server; request; key} <: communication_states a);*
  trigger_event client (CommClientSendRequest client server payload_bytes key);*
  let req_payload:com_message_t = RequestMessage {request=payload_bytes; key} in
  let*? msg_id = send_confidential comm_keys_ids client server req_payload in
  let req_meta_data:comm_meta_data a = {key; server; sid; request} in
  return (Some (msg_id, req_meta_data))

[@@ "opaque_to_smt"]
val receive_request:
  {|comm_layer_reqres_tag|} ->
  #a:Type -> {|comparse_parser_serializer a|} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (a & comm_meta_data a))
let receive_request #tag #a #ps comm_keys_ids server msg_id =
  let*? req_msg_t:com_message_t = receive_confidential comm_keys_ids server msg_id in
  guard_tr (RequestMessage? req_msg_t);*?
  let RequestMessage req_msg = req_msg_t in
  let*? request = return (parse a #ps_able req_msg.request) in
  trigger_event server (CommServerReceiveRequest server req_msg.request req_msg.key);*
  let* sid = new_session_id server in
  set_state server sid (ServerReceiveRequest {request; key=req_msg.key} <: communication_states a);*
  let req_meta_data:comm_meta_data a = {key=req_msg.key; server; sid; request} in
  return (Some (request, req_meta_data))

[@@ "opaque_to_smt"]
val mk_comm_layer_response_nonce: #a:Type -> {|comparse_parser_serializer a|} -> comm_meta_data a -> usage -> traceful (option bytes)
let mk_comm_layer_response_nonce #a #ps_a req_meta_data usg =
  let* tr = get_trace in
  let* nonce = mk_rand usg (get_label #default_crypto_usages tr req_meta_data.key) 32 in
  return (Some nonce)

[@@ "opaque_to_smt"]
val mk_comm_layer_response_nonce_labeled: #a:Type -> {|comparse_parser_serializer a|} -> comm_meta_data a -> usage -> label -> traceful (option bytes)
let mk_comm_layer_response_nonce_labeled #a #ps_a req_meta_data usg lab =
  let* tr = get_trace in
  let lab_join = join lab (get_label #default_crypto_usages tr req_meta_data.key) in
  let* nonce = mk_rand usg lab_join 32 in
  return (Some nonce)

[@@ "opaque_to_smt"]
val compute_response_message:
  #a:Type -> {|comparse_parser_serializer a|} ->
  principal -> bytes -> bytes -> a -> bytes
let compute_response_message #a #ps server key nonce response =
  let res_bytes = serialize a #ps_able response in
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  let ciphertext = aead_enc key nonce res_bytes ad_bytes in
  serialize com_message_t (ResponseMessage {nonce; ciphertext})

[@@ "opaque_to_smt"]
val send_response:
  {|comm_layer_reqres_tag|} ->
  #a:eqtype -> {|comparse_parser_serializer a|} ->
  principal -> comm_meta_data a -> a -> traceful (option timestamp)
let send_response #tag #a #ps server req_meta_data response =
  let*? state = get_state server req_meta_data.sid in
  guard_tr (ServerReceiveRequest? state);*?
  let ServerReceiveRequest srr = state in
  guard_tr (srr.key = req_meta_data.key);*?
  guard_tr (srr.request = req_meta_data.request);*?
  trigger_event server (CommServerSendResponse server (serialize a #ps_able srr.request) (serialize a #ps_able response));*
  let* nonce = mk_rand NoUsage public 32 in
  let resp_msg = compute_response_message server req_meta_data.key nonce response in
  let* msg_id = send_msg resp_msg in
  return (Some msg_id)

[@@ "opaque_to_smt"]
val decode_response_message:
  {|comm_layer_reqres_tag|} ->
  #a:Type -> {|comparse_parser_serializer a|} ->
  principal -> bytes -> bytes -> option a
let decode_response_message #tag #a #ps server key msg_bytes =
  let? resp_env_t:com_message_t = parse com_message_t msg_bytes in
  guard (ResponseMessage? resp_env_t);?
  let ResponseMessage resp_env = resp_env_t in
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  let? resp_bytes = aead_dec key resp_env.nonce resp_env.ciphertext ad_bytes in
  let? resp = parse a #ps_able resp_bytes in
  Some resp

[@@ "opaque_to_smt"]
val receive_response:
  {|comm_layer_reqres_tag|} ->
  #a:Type -> {|comparse_parser_serializer a|} ->
  principal -> comm_meta_data a -> timestamp ->
  traceful (option (a & comm_meta_data a))
let receive_response #tag #a #ps client req_meta_data msg_id =
  let*? state:communication_states a = get_state client req_meta_data.sid in
  guard_tr (ClientSendRequest? state);*?
  let ClientSendRequest csr = state in
  let*? resp_msg_bytes = recv_msg msg_id in
  let*? payload = return (decode_response_message csr.server csr.key resp_msg_bytes) in
  guard_tr (csr.server = req_meta_data.server);*?
  guard_tr (csr.key = req_meta_data.key);*?
  set_state client req_meta_data.sid (ClientReceiveResponse {server=csr.server; response=payload; key=csr.key} <: communication_states a);*
  trigger_event client (CommClientReceiveResponse client csr.server (serialize a #ps_able payload) csr.key);*
  return (Some (payload, req_meta_data))
