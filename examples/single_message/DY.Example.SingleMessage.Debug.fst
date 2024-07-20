module DY.Example.SingleMessage.Debug

open DY.Core
open DY.Lib
open DY.Example.SingleMessage.Protocol.Stateful

(*** Example Protocol Run with Trace Printing ***)

let debug () : traceful (option unit) =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  (*** Initialize protocol run ***)
  let client = "client" in
  let server = "server" in

  let*? client_comm_keys_sess_ids, server_comm_keys_sess_ids = initialize_communication client server in

  // Client prepare message
  let* client_session_id = prepare_message client server in

  // Client send message
  let*? msg_id = send_message client_comm_keys_sess_ids client server client_session_id in

  // Server receive message
  let*? server_session_id = receive_message server_comm_keys_sess_ids server msg_id in

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string default_trace_to_string_printers tr
    ) in
  
  return (Some ())

//Run ``debug ()`` when the module loads
#push-options "--warn_error -272"
let _ = debug () Nil
#pop-options