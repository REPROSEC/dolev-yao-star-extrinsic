module DY.Lib.Communication.Printing

open Comparse
open DY.Core

open DY.Lib.Printing
open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.RequestResponse

#set-options "--fuel 0 --ifuel 1 --z3cliopt 'smt.qi.eager_threshold=100'"

val comm_message_to_string:
  #core_type:Type0 -> {|comm_layer_core_config core_type|} ->
  #reqres_type:Type0 -> {|comm_layer_reqres_config reqres_type|} -> 
  (core_type -> string) -> (reqres_type -> string) -> (bytes -> string) -> bytes ->
  option string
let comm_message_to_string #core_type #core_config #reqres_type #reqres_config msg_to_string reqres_payload_to_string other_messages_to_string b =
  match b with
  | PkeEnc pk nonce msg -> (
    match parse (encryption_input comm_message_t) #(parseable_serializeable_bytes_encryption_input #comm_message_t #(comm_layer_tag_core_config_reqres reqres_type)) msg with
    | Some (Unsigned payload) -> (
      match payload with
      | SigMessage _ -> Some "Error: SigMessage cannot be inside a PkeEnc encryption"
      | RequestMessage {request; key} -> (
        let? request_parsed = parse reqres_type request in 
        Some (reqres_payload_to_string request_parsed)
      )
      | ResponseMessage _ -> Some "Error: ResponseMessage cannot be inside a PkeEnc encryption"
    )
    | Some (Signed _ _ _) -> Some "Error: Signed encryption_input cannot be inside a PkeEnc encryption outside a signature"
    | None -> (
      match parse (encryption_input core_type) msg with
      | Some (Unsigned payload) -> (
        Some (Printf.sprintf "pk_enc (pk = %s, msg = (%s))"
          (bytes_to_string pk) (msg_to_string payload))
      )
      | Some (Signed _ _ _) -> Some "Error: Signed encryption_input cannot be inside a PkeEnc encryption outside a signature"
      | None -> Some (other_messages_to_string b)
    )
  )
  | _ -> (
    match parse comm_message_t b with
    | Some (SigMessage {msg; signature}) -> (
      match parse (signature_input core_type) msg with
      | Some si -> (
        let sender, receiver, payload = (
          match si with
          | Plain sender receiver payload -> (
            sender, receiver, msg_to_string payload)
          | Encrypted payload _ -> (
            match payload with
            | PkeEnc pk nonce payload_plain -> (
              match parse (encryption_input core_type) payload_plain with
              | Some (Signed sender receiver payload) -> (sender, receiver, (
                Printf.sprintf "pk_enc (pk = %s, msg = (%s))"
                  (bytes_to_string pk) (msg_to_string payload))
              )
              | _ -> ("Error: Signed encryption_input does not contain a Signed message -- " ^ (bytes_to_string payload_plain), "","")
            )
            | _ -> ("Error: Encrypted signature_input does not contain a PkeEnc encrypted message -- " ^ (bytes_to_string payload), "", "")
          )
        ) in
        Some (Printf.sprintf "msg = (<BREAK>\tsender = %s,<BREAK>\treceiver = %s,<BREAK>\tpayload = (%s<BREAK>\t)<BREAK>),<BREAK>signature = sig(sk_{%s}, msg)" sender receiver payload sender)
      )
      | None -> Some "Error: signed_communication_message does not contain a signature_input"
    )
    | Some (RequestMessage _) -> Some "Error: RequestMessage cannot be send in plaintext"
    | Some (ResponseMessage {nonce; ciphertext}) -> (
      match ciphertext with
      | AeadEnc key nonce response ad -> (
        let? response_parsed = parse reqres_type response in 
        Some (reqres_payload_to_string response_parsed)
      )
      | _ -> Some "Error: response_envelope does not contain an AEAD ciphertext"
    )
    | None -> Some (other_messages_to_string b)
  )

val com_core_event_to_string:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  (a -> string) ->
  (string & (bytes -> option string))
let com_core_event_to_string #a payload_to_string =
  ((event_communication_core_event a).tag, (fun b -> (
    let? ce = parse (communication_core_event a) b in
    match ce with
    | CommConfSendMsg sender receiver payload ->
      Some (Printf.sprintf "CommConfSendMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (payload_to_string payload))
    | CommConfReceiveMsg receiver payload ->
      Some (Printf.sprintf "CommConfReceiveMsg receiver = %s, payload = (%s)"
        receiver (payload_to_string payload))
    | CommAuthSendMsg sender payload ->
      Some (Printf.sprintf "CommAuthSendMsg sender = %s, payload = (%s)"
        sender (payload_to_string payload))
    | CommAuthReceiveMsg sender receiver payload -> 
      Some (Printf.sprintf "CommAuthReceiveMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (payload_to_string payload))
    | CommConfAuthSendMsg sender receiver payload -> 
      Some (Printf.sprintf "CommConfAuthSendMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (payload_to_string payload))
    | CommConfAuthReceiveMsg sender receiver payload ->
      Some (Printf.sprintf "CommConfAuthReceiveMsg sender = %s, receiver = %s, payload = (%s)"
        sender receiver (payload_to_string payload))
  )))

val com_reqres_event_to_string:
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  (a -> string) -> 
  (string & (bytes -> option string))
let com_reqres_event_to_string #a payload_to_string =
  ((event_communication_reqres_event #a).tag, (fun b -> (
    let? cre = parse (communication_reqres_event a) b in
    match cre with
    | CommClientSendRequest client server request key -> (
      Some (Printf.sprintf "CommClientSendRequest client = %s, server = %s, request = (%s)"
        client server (payload_to_string request))
    )
    | CommServerReceiveRequest server request key -> (
      Some (Printf.sprintf "CommServerReceiveRequest server = %s, request = (%s), key = %s"
        server (payload_to_string request) (bytes_to_string key))
    )
    | CommServerSendResponse server request response key -> (
      Some (Printf.sprintf "CommServerSendResponse server = %s, request = %s, response = (%s), key = %s"
        server (payload_to_string request) (payload_to_string response) (bytes_to_string key))
    )
    | CommClientReceiveResponse client server request response key -> (
      Some (Printf.sprintf "CommClientReceiveResponse client = %s, server = %s, response = (%s), key = %s" 
        client server (payload_to_string response) (bytes_to_string key))
    )
  )))

val com_event_to_string:
  #core_type:Type0 -> {|comm_layer_core_config core_type|} ->
  #reqres_type:Type0 -> {|comm_layer_reqres_config reqres_type|} ->
  (core_type -> string) -> (reqres_type -> string) ->
  list (string & (bytes -> option string))
let com_event_to_string #core_type #reqres_type core_payload_to_string reqres_payload_to_string =
  [com_core_event_to_string core_payload_to_string;
    com_reqres_event_to_string reqres_payload_to_string]

val com_state_to_string: (#a:Type0) -> {|comm_layer_reqres_config a|} -> (a -> string) -> (string & (bytes -> option string))
let com_state_to_string #a payload_to_string =
  ((local_state_communication_layer_session a).tag, (fun b -> (
    let? cs = parse (communication_states a) b in
    match cs with
    | ClientSendRequest {server; request; key} -> 
      Some (Printf.sprintf "ClientSendRequest server = %s, payload = (%s), key = %s" 
        server (payload_to_string request) (bytes_to_string key))
    | ServerReceiveRequest {request; key} -> 
      Some (Printf.sprintf "ServerReceiveRequest payload = (%s), key = %s"
        (payload_to_string request) (bytes_to_string key)) 
    | ClientReceiveResponse {server; response; key} -> 
      Some (Printf.sprintf "ClientReceiveResponse server = %s, payload = (%s), key = %s"
        server (payload_to_string response) (bytes_to_string key))
  )))
