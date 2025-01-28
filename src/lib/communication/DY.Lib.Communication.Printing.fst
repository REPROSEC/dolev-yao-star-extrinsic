module DY.Lib.Communication.Printing

open Comparse
open DY.Core

open DY.Lib.Printing
open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.RequestResponse

#set-options "--fuel 0 --ifuel 1 --z3cliopt 'smt.qi.eager_threshold=100'"

val com_message_to_string: (bytes -> option string) -> (bytes -> option string) -> bytes -> option string
let com_message_to_string msg_to_string reqres_payload_to_string b =
  match b with
  | PkeEnc pk nonce msg -> (
    match parse com_message_t msg with
    | Some (SigMessage _) -> Some "Error: SigMessage cannot be inside a PkeEnc encryption"
    | Some (RequestMessage {request; key}) -> reqres_payload_to_string request
    | Some (ResponseMessage _) -> Some "Error: ResponseMessage cannot be inside a PkeEnc encryption"
    | None -> Some (option_to_string msg_to_string b)
  )
  | _ -> (
    match parse com_message_t b with
    | Some (SigMessage {msg; signature}) -> (
      match parse signature_input msg with
      | Some si -> (
        let sender, receiver, payload = (
          match si with
          | Plain sender receiver payload -> sender, receiver, (option_to_string msg_to_string payload)
          | Encrypted sender receiver payload _ -> sender, receiver, (
            match parse com_send_byte payload with
            | Some {b} -> (
              match b with
              | PkeEnc pk nonce msg -> (
                Printf.sprintf "pk_enc (pk = %s, msg = (%s))"
                  (bytes_to_string pk) (option_to_string msg_to_string msg))
              | _ -> "Error: com_send_byte message does not contain a PkeEnc encrypted message"
            )
            | None -> "Error: encrypted signature input does not contain a com_send_byte message"
          )
        ) in
        Some (Printf.sprintf "msg = (<BREAK>\tsender = %s,<BREAK>\treceiver = %s,<BREAK>\tpayload = (%s<BREAK>\t)<BREAK>),<BREAK>signature = sig(sk_{%s}, msg)" sender receiver payload sender)
      )
      | None -> Some "Error: signed_communication_message does not contain a signature_input"
    )
    | Some (RequestMessage _) -> Some "Error: RequestMessage cannot be send in plaintext"
    | Some (ResponseMessage {nonce; ciphertext}) -> (
      match ciphertext with
      | AeadEnc key nonce msg ad -> reqres_payload_to_string msg
      | _ -> Some "Error: response_envelope does not contain an AEAD ciphertext"
    )
    | None -> Some (option_to_string msg_to_string b)
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
    | CommClientSendRequest client server request key -> 
      Some (Printf.sprintf "CommClientSendRequest client = %s, server = %s, request = (%s)"
        client server (option_to_string payload_to_string request))
    | CommServerReceiveRequest server request key -> 
      Some (Printf.sprintf "CommServerReceiveRequest server = %s, request = (%s), key = %s"
        server (option_to_string payload_to_string request) (bytes_to_string key))
    | CommServerSendResponse server request response -> 
      Some (Printf.sprintf "CommServerSendResponse server = %s, request = %s, response = (%s)"
        server (option_to_string payload_to_string request) (option_to_string payload_to_string response))
    | CommClientReceiveResponse client server response key -> 
      Some (Printf.sprintf "CommClientReceiveResponse client = %s, server = %s, response = (%s), key = %s" 
        client server (option_to_string payload_to_string response) (bytes_to_string key))
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
    | ClientSendRequest {server; request; key} -> 
      Some (Printf.sprintf "ClientSendRequest server = %s, payload = (%s), key = %s" 
        server (option_to_string payload_to_string request) (bytes_to_string key))
    | ServerReceiveRequest {request; key} -> 
      Some (Printf.sprintf "ServerReceiveRequest payload = (%s), key = %s"
        (option_to_string payload_to_string request) (bytes_to_string key)) 
    | ClientReceiveResponse {server; response; key} -> 
      Some (Printf.sprintf "ClientReceiveResponse server = %s, payload = (%s), key = %s"
        server (option_to_string payload_to_string response) (bytes_to_string key))
  )))
