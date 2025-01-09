module DY.Lib.Communication.Printing

open Comparse
open DY.Core

open DY.Lib.Printing
open DY.Lib.Communication.Core
open DY.Lib.Communication.RequestResponse

#set-options "--fuel 0 --ifuel 1 --z3cliopt 'smt.qi.eager_threshold=100'"

val com_message_to_string: (bytes -> option string) -> (bytes -> option string) -> bytes -> option string
let com_message_to_string core_payload_to_string reqres_payload_to_string b =
  match parse signed_communication_message b with
  | Some scm -> (
    match parse signature_input scm.msg with
    | Some si -> (
      let sender, receiver, payload = (
        match si with
        | Plain sender receiver payload -> sender, receiver, payload
        | Encrypted sender receiver payload _ -> sender, receiver, (
          match payload with
          | PkeEnc pk nonce msg -> msg
          | _ -> empty
        )
      ) in
      Some (Printf.sprintf "msg = (%s, %s, (%s)), signature = sig(sk_{%s}, msg)" sender receiver (option_to_string core_payload_to_string payload) sender)
    )
    | None -> Some "Error: signed_communication_message does not contain a signature_input"
  )
  | None -> (
    match b with
    | PkeEnc pk nonce msg -> (
      match parse request_message b with
      | Some {payload; key} ->
        Some (Printf.sprintf "Request payload = (%s), key = %s" 
          (option_to_string reqres_payload_to_string payload) (bytes_to_string key))
      | None -> Some (option_to_string core_payload_to_string b)
    )
    | _ -> (
      match parse response_envelope b with
        | Some {nonce; ciphertext} -> (
          match ciphertext with
          | AeadEnc key nonce msg ad -> (
            Some (Printf.sprintf "Response payload = (%s)"
              (option_to_string reqres_payload_to_string msg))
          )
          | _ -> Some "Error: response_envelope does not contain an AEAD ciphertext"
        )
        | None -> Some "Error not a communication layer message"
    )
  )


val com_core_event_to_string: (bytes -> option string) -> (string & (bytes -> option string))
let com_core_event_to_string payload_to_string =
  (event_communication_event.tag, (fun b -> (
    let? ce = parse communication_event b in
    match ce with
    | CommConfSendMsg sender receiver payload ->
      Some (Printf.sprintf "CommConfSendMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (option_to_string payload_to_string payload))
    | CommConfReceiveMsg receiver payload ->
      Some (Printf.sprintf "CommConfReceiveMsg receiver = %s, payload = (%s)"
        receiver (option_to_string payload_to_string payload))
    | CommAuthSendMsg sender payload ->
      Some (Printf.sprintf "CommAuthSendMsg sender = %s, payload = (%s)"
        sender (option_to_string payload_to_string payload))
    | CommAuthReceiveMsg sender receiver payload -> 
      Some (Printf.sprintf "CommAuthReceiveMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (option_to_string payload_to_string payload))
    | CommConfAuthSendMsg sender receiver payload -> 
      Some (Printf.sprintf "CommConfAuthSendMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (option_to_string payload_to_string payload))
    | CommConfAuthReceiveMsg sender receiver payload ->
      Some (Printf.sprintf "CommConfAuthReceiveMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (option_to_string payload_to_string payload))
  )))

val com_reqres_event_to_string: (bytes -> option string) -> (string & (bytes -> option string))
let com_reqres_event_to_string payload_to_string =
  (event_communication_reqres_event.tag, (fun b -> (
    let? cre = parse communication_reqres_event b in
    match cre with
    | CommClientSendRequest client server payload key -> 
      Some (Printf.sprintf "CommClientSendRequest client = %s, server = %s, payload = (%s)"
        client server (option_to_string payload_to_string payload))
    | CommServerReceiveRequest server payload key -> 
      Some (Printf.sprintf "CommServerReceiveRequest server = %s, payload = (%s), key = %s"
        server (option_to_string payload_to_string payload) (bytes_to_string key))
    | CommServerSendResponse server payload -> 
      Some (Printf.sprintf "CommServerSendResponse server = %s, payload = (%s)"
        server (option_to_string payload_to_string payload))
    | CommClientReceiveResponse client server payload key -> 
      Some (Printf.sprintf "CommClientReceiveResponse client = %s, server = %s, payload = (%s), key = %s" 
        client server (option_to_string payload_to_string payload) (bytes_to_string key))
  )))

val com_event_to_string:
  (bytes -> option string) -> (bytes -> option string) ->
  list (string & (bytes -> option string))
let com_event_to_string core_payload_to_string reqres_payload_to_string =
  [com_core_event_to_string core_payload_to_string;
    com_reqres_event_to_string reqres_payload_to_string]

val com_state_to_string: (bytes -> option string) -> (string & (bytes -> option string))
let com_state_to_string payload_to_string =
  (local_state_communication_layer_session.tag, (fun b -> (
    let? cs = parse communication_states b in
    match cs with
    | ClientSendRequest {server; payload; key} -> 
      Some (Printf.sprintf "ClientSendRequest server = %s, payload = (%s), key = %s" 
        server (option_to_string payload_to_string payload) (bytes_to_string key))
    | ServerReceiveRequest {payload; key} -> 
      Some (Printf.sprintf "ServerReceiveRequest payload = (%s), key = %s"
        (option_to_string payload_to_string payload) (bytes_to_string key)) 
    | ClientReceiveResponse {server; payload; key} -> 
      Some (Printf.sprintf "ClientReceiveResponse server = %s, payload = (%s), key = %s"
        server (option_to_string payload_to_string payload) (bytes_to_string key))
  )))
