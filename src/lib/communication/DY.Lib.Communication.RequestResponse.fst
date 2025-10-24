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

instance comm_layer_tag_core_config_reqres (a:Type) {|config:comm_layer_reqres_config a|}: comm_layer_core_config comm_message_t = {
  core_tag = config.reqres_tag ^ ".CoreConfig.ReqRes";
  core_ps_a = ps_comm_message_t;
}

val comm_layer_aead_tag: a:Type -> {|comm_layer_reqres_config a|} -> string
let comm_layer_aead_tag a #config = config.reqres_tag ^ ".Aead.Key"

[@@with_bytes bytes]
type comm_meta_data (a:Type) {|config:comm_layer_reqres_config a|} = {
  key:bytes;
  server:principal;
  sid:state_id;
  [@@@ with_parser #bytes config.reqres_ps_a]
  request:a;
}

%splice [ps_comm_meta_data] (gen_parser (`comm_meta_data))
%splice [ps_comm_meta_data_is_well_formed] (gen_is_well_formed_lemma (`comm_meta_data))

[@@"opaque_to_smt"]
val get_response_label: tr:trace -> #a:Type0 -> {|comm_layer_reqres_config a|} -> comm_meta_data a -> label
let get_response_label tr #a #ps req_meta_data = get_label #default_crypto_usages tr req_meta_data.key


(*** States ***)

[@@with_bytes bytes]
type client_send_request (a:Type) {|config:comm_layer_reqres_config a|}  = {
  server:principal;
  [@@@ with_parser #bytes config.reqres_ps_a]
  request:a;
  key:bytes
}

%splice [ps_client_send_request] (gen_parser (`client_send_request))
%splice [ps_client_send_request_is_well_formed] (gen_is_well_formed_lemma (`client_send_request))

[@@with_bytes bytes]
type server_receive_request (a:Type) {|config:comm_layer_reqres_config a|}  = {
  [@@@ with_parser #bytes config.reqres_ps_a]
  request:a;
  key:bytes
}

%splice [ps_server_receive_request] (gen_parser (`server_receive_request))
%splice [ps_server_receive_request_is_well_formed] (gen_is_well_formed_lemma (`server_receive_request))

[@@with_bytes bytes]
type client_receive_response (a:Type) {|config:comm_layer_reqres_config a|}  = {
  server:principal;
  [@@@ with_parser #bytes config.reqres_ps_a]
  response:a;
  key:bytes
}

%splice [ps_client_receive_response] (gen_parser (`client_receive_response))
%splice [ps_client_receive_response_is_well_formed] (gen_is_well_formed_lemma (`client_receive_response))

[@@with_bytes bytes]
type communication_states (a:Type) {|c:comm_layer_reqres_config a|}  =
  | ClientSendRequest: client_send_request a -> communication_states a
  | ServerReceiveRequest: server_receive_request a -> communication_states a
  | ClientReceiveResponse: client_receive_response a -> communication_states a

#push-options "--ifuel 1"
%splice [ps_communication_states] (gen_parser (`communication_states))
%splice [ps_communication_states_is_well_formed] (gen_is_well_formed_lemma (`communication_states))
#pop-options

instance parseable_serializeable_bytes_communication_states (a:Type) {|comm_layer_reqres_config a|}: parseable_serializeable bytes (communication_states a)
  = mk_parseable_serializeable (ps_communication_states a)

instance local_state_communication_layer_session (a:Type) {|config:comm_layer_reqres_config a|}: local_state (communication_states a) = {
  tag = config.reqres_tag ^ ".State";
  format = parseable_serializeable_bytes_communication_states a;
}

[@@with_bytes bytes]
type communication_reqres_event (a:Type) {|config:comm_layer_reqres_config a|} =
  | CommClientSendRequest: client:principal -> server:principal -> [@@@ with_parser #bytes config.reqres_ps_a] request:a -> key:bytes -> communication_reqres_event a
  | CommServerReceiveRequest: server:principal -> [@@@ with_parser #bytes config.reqres_ps_a] request:a -> key:bytes -> communication_reqres_event a
  | CommServerSendResponse: server:principal -> [@@@ with_parser #bytes config.reqres_ps_a] request:a -> [@@@ with_parser #bytes config.reqres_ps_a] response:a -> key:bytes -> communication_reqres_event a
  | CommClientReceiveResponse: client:principal -> server:principal -> [@@@ with_parser #bytes config.reqres_ps_a] request:a -> [@@@ with_parser #bytes config.reqres_ps_a] response:a -> key:bytes -> communication_reqres_event a

#push-options "--ifuel 1"
%splice [ps_communication_reqres_event] (gen_parser (`communication_reqres_event))
%splice [ps_communication_reqres_event_is_well_formed] (gen_is_well_formed_lemma (`communication_reqres_event))
#pop-options

instance event_communication_reqres_event (#a:Type) {|config:comm_layer_reqres_config a|}: event (communication_reqres_event a) = {
  tag = config.reqres_tag ^ ".Event";
  format = mk_parseable_serializeable (ps_communication_reqres_event a);
}


(*** API ***)

[@@ "opaque_to_smt"]
val send_request:
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option (timestamp & comm_meta_data a))
let send_request #a #config comm_keys_ids client server request =
  let* key = mk_rand (AeadKey (comm_layer_aead_tag a) empty) (comm_label client server) 32 in
  trigger_event client (CommClientSendRequest client server request key <: communication_reqres_event a);*
  let payload_bytes:bytes = serialize a request in
  let* sid = new_session_id client in
  set_state client sid (ClientSendRequest {server; request; key} <: communication_states a);*
  let req_payload:comm_message_t = RequestMessage {request=payload_bytes; key} in
  let*? msg_id = send_confidential #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids client server req_payload in
  let req_meta_data:comm_meta_data a = {key; server; sid; request} in
  return (Some (msg_id, req_meta_data))

[@@ "opaque_to_smt"]
val receive_request:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (a & comm_meta_data a))
let receive_request #a comm_keys_ids server msg_id =
  let*? req_msg_t:comm_message_t = receive_confidential #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids server msg_id in
  guard_tr (RequestMessage? req_msg_t);*?
  let RequestMessage req_msg = req_msg_t in
  let*? request = return (parse a req_msg.request) in
  trigger_event server (CommServerReceiveRequest server request req_msg.key <: communication_reqres_event a);*
  let* sid = new_session_id server in
  set_state server sid (ServerReceiveRequest {request; key=req_msg.key} <: communication_states a);*
  let req_meta_data:comm_meta_data a = {key=req_msg.key; server; sid; request} in
  return (Some (request, req_meta_data))

[@@ "opaque_to_smt"]
val mk_comm_layer_response_nonce: #a:Type -> {|comm_layer_reqres_config a|} -> comm_meta_data a -> usage -> traceful (option bytes)
let mk_comm_layer_response_nonce #a req_meta_data usg =
  let* tr = get_trace in
  let* nonce = mk_rand usg (get_response_label tr req_meta_data) 32 in
  return (Some nonce)

[@@ "opaque_to_smt"]
val mk_comm_layer_response_nonce_labeled: #a:Type -> {|comm_layer_reqres_config a|} -> comm_meta_data a -> usage -> label -> traceful (option bytes)
let mk_comm_layer_response_nonce_labeled #a req_meta_data usg lab =
  let* tr = get_trace in
  let lab_join = join lab (get_response_label tr req_meta_data) in
  let* nonce = mk_rand usg lab_join 32 in
  return (Some nonce)

[@@ "opaque_to_smt"]
val compute_response_message:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a -> bytes -> a -> bytes
let compute_response_message #a server req_meta_data nonce response =
  let res_bytes = serialize a response in
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  let ciphertext = aead_enc req_meta_data.key nonce res_bytes ad_bytes in
  serialize comm_message_t (ResponseMessage {nonce; ciphertext})

[@@ "opaque_to_smt"]
val send_response:
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a -> a -> traceful (option timestamp)
let send_response #a server req_meta_data response =
  let*? state = get_state server req_meta_data.sid in
  guard_tr (ServerReceiveRequest? state);*?
  let ServerReceiveRequest srr = state in
  guard_tr (srr.key = req_meta_data.key);*?
  guard_tr (srr.request = req_meta_data.request);*?
  trigger_event server (CommServerSendResponse server srr.request response req_meta_data.key <: communication_reqres_event a);*
  let* nonce = mk_rand NoUsage public 32 in
  let resp_msg = compute_response_message server req_meta_data nonce response in
  let* msg_id = send_msg resp_msg in
  return (Some msg_id)

[@@ "opaque_to_smt"]
val decode_response_message:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> bytes -> bytes -> option a
let decode_response_message #a server key msg_bytes =
  let? resp_env_t:comm_message_t = parse comm_message_t msg_bytes in
  guard (ResponseMessage? resp_env_t);?
  let ResponseMessage resp_env = resp_env_t in
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  let? resp_bytes = aead_dec key resp_env.nonce resp_env.ciphertext ad_bytes in
  let? resp = parse a resp_bytes in
  Some resp

[@@ "opaque_to_smt"]
val receive_response:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a -> timestamp ->
  traceful (option (a & comm_meta_data a))
let receive_response #a client req_meta_data msg_id =
  let*? state:communication_states a = get_state client req_meta_data.sid in
  guard_tr (ClientSendRequest? state);*?
  let ClientSendRequest csr = state in
  let*? resp_msg_bytes = recv_msg msg_id in
  let*? payload = return (decode_response_message csr.server csr.key resp_msg_bytes) in
  guard_tr (csr.server = req_meta_data.server);*?
  guard_tr (csr.key = req_meta_data.key);*?
  set_state client req_meta_data.sid (ClientReceiveResponse {server=csr.server; response=payload; key=csr.key} <: communication_states a);*
  trigger_event client (CommClientReceiveResponse client csr.server req_meta_data.request payload csr.key <: communication_reqres_event a);*
  return (Some (payload, req_meta_data))


(**** Layer Initialization ****)

[@@ "opaque_to_smt"]
val initialize_communication_reqres: a:Type -> {|comm_layer_reqres_config a|} -> principal -> principal -> traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
let initialize_communication_reqres a client server = initialize_communication_core comm_message_t #(comm_layer_tag_core_config_reqres a) client server
