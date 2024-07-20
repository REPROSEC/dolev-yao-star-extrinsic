module DY.Example.SingleMessage.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleMessage.Protocol.Total

(*** State type ***)

[@@with_bytes bytes]
type login_state =
  | ClientState: server:principal -> secret:bytes -> login_state
  | ServerState: secret:bytes -> login_state

%splice [ps_login_state] (gen_parser (`login_state))
%splice [ps_login_state_is_well_formed] (gen_is_well_formed_lemma (`login_state))

instance parseable_serializeable_bytes_login_state: parseable_serializeable bytes login_state
 = mk_parseable_serializeable ps_login_state

instance local_state_login_state: local_state login_state = {
  tag = "Login.State";
  format = parseable_serializeable_bytes_login_state;
}

(*** Event type ***)

[@@with_bytes bytes]
type login_event =
  | ClientSendMsg: client:principal -> server:principal -> secret:bytes -> login_event
  | ServerReceivedMsg: client:principal -> server:principal -> secret:bytes -> login_event

%splice [ps_login_event] (gen_parser (`login_event))
%splice [ps_login_event_is_well_formed] (gen_is_well_formed_lemma (`login_event))

instance event_login_event: event login_event = {
  tag = "Login.Event";
  format = mk_parseable_serializeable ps_login_event;
}

(*** Stateful code ***)

val prepare_message: principal -> principal -> traceful state_id
let prepare_message client server =
  let* secret = mk_rand NoUsage (join (principal_label client) (principal_label server)) 32 in
  trigger_event client (ClientSendMsg client server secret);*
  let* state_id = new_session_id client in
  set_state client state_id (ClientState server secret <: login_state);*
  return state_id

val send_message: communication_keys_sess_ids -> principal -> principal -> state_id -> traceful (option timestamp)
let send_message comm_keys_ids client server state_id =
  let*? st:login_state = get_state client state_id in
  match st with
  | ClientState server secret -> (
    let msg = compute_message secret in
    let*? msg_id = send_confidential comm_keys_ids client server msg in
    return (Some msg_id)
  )
  | _ -> return None

val receive_message: communication_keys_sess_ids -> principal -> timestamp -> traceful (option state_id)
let receive_message comm_keys_ids server msg_id =
  let*? msg:communication_message = receive_confidential comm_keys_ids server msg_id in
  let*? single_msg:single_message = return (decode_message msg.payload) in
  trigger_event server (ServerReceivedMsg msg.sender server single_msg.secret);*
  let* state_id = new_session_id server in
  set_state server state_id (ServerState single_msg.secret <: login_state);*
  return (Some state_id)