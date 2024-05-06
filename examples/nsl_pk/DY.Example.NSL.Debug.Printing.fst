module DY.Example.NSL.Debug.Printing

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total
open DY.Example.NSL.Protocol.Stateful

/// This module is not needed for modeling
/// the protocol. The purpose of this model
/// is to provide functions to nicely print
/// the trace to the console.

(*** Convert NSL Messages to String ***)

val decrypt_message: bytes -> bytes -> bytes -> option bytes
let decrypt_message sk_a sk_b msg_bytes =
  let msg_plain = pk_dec sk_a msg_bytes in
  match msg_plain with
  | Some msg -> msg_plain
  | None -> (
    pk_dec sk_b msg_bytes
  )

val message_to_string: bytes -> bytes -> bytes -> option string
let message_to_string sk_a sk_b msg_bytes =
  let? msg_plain = decrypt_message sk_a sk_b msg_bytes in
  let? msg = parse message msg_plain in
  match msg with
  | Msg1 msg1 -> Some (Printf.sprintf "PkEnc[sk=(%s), msg=(n_a=(%s), principal=%s)]" (bytes_to_string sk_b) (bytes_to_string msg1.n_a) msg1.alice)
  | Msg2 msg2 -> (
    Some (Printf.sprintf "PkEnc[sk=(%s), msg=(n_a=(%s), n_b=(%s), principal=%s)]"
            (bytes_to_string sk_a) (bytes_to_string msg2.n_a) (bytes_to_string msg2.n_b) msg2.bob)
  )
  | Msg3 msg3 -> Some (Printf.sprintf "PkEnc[sk=(%s), msg=(n_b=(%s))]" (bytes_to_string sk_b) (bytes_to_string msg3.n_b))


(*** Convert NSL Sessions to String ***)

val session_to_string: bytes -> option string
let session_to_string sess_bytes =
  let? sess = parse nsl_session sess_bytes in
  match sess with
  | InitiatorSentMsg1 b n_a -> (
    Some (Printf.sprintf "[principal=%s, n_a=(%s)]" b (bytes_to_string n_a))
  )
  | ResponderSentMsg2 a n_a n_b -> (
    Some (Printf.sprintf "[principal=%s, n_a=(%s), n_b=(%s)]" a (bytes_to_string n_a) (bytes_to_string n_b))
  )
  | InitiatorSentMsg3 b n_a n_b -> (
    Some (Printf.sprintf "[principal=%s, n_a=(%s), n_b=(%s)]" b (bytes_to_string n_a) (bytes_to_string n_b))
  )
  | ResponderReceivedMsg3 a n_a n_b -> (
    Some (Printf.sprintf "[principal=%s, n_a=(%s), n_b=(%s)]" a (bytes_to_string n_a) (bytes_to_string n_b))
  )


(*** Convert NSL Events to String ***)

val event_to_string: bytes -> option string
let event_to_string event_bytes =
  let? event = parse nsl_event event_bytes in
  match event with
  | Initiate1 a b n_a -> (
    Some (Printf.sprintf "[principal1=%s, principal2=(%s), n_b=(%s)]" a b (bytes_to_string n_a))
  )
  | Respond1 a b n_a n_b -> (
    Some (Printf.sprintf "[principal1=%s, principal2=(%s), n_a=(%s), n_b=(%s)]" a b (bytes_to_string n_a) (bytes_to_string n_b))
  )
  | Initiate2 a b n_a n_b -> (
    Some (Printf.sprintf "[principal1=%s, principal2=(%s), n_a=(%s), n_b=(%s)]" a b (bytes_to_string n_a) (bytes_to_string n_b))
  )
  | Respond2 a b n_a n_b -> (
    Some (Printf.sprintf "[principal1=%s, principal2=(%s), n_a=(%s), n_b=(%s)]" a b (bytes_to_string n_a) (bytes_to_string n_b))
  )


(*** Putting Everything Together ***)

val get_nsl_trace_to_string_printers: bytes -> bytes -> trace_to_string_printers
let get_nsl_trace_to_string_printers priv_key_alice priv_key_bob = 
  trace_to_string_printers_builder 
    (message_to_string priv_key_alice priv_key_bob)
    [(nsl_session_tag, session_to_string)]
    [(event_nsl_event.tag, event_to_string)]
