module DY.Lib.Printing

open Comparse
open DY.Core
open DY.Lib.State.Labeled
open DY.Lib.State.Map

/// This module provides functions to convert types
/// from DY* to a string. These functions are used to
/// print the trace from an example protocol run.
///
/// As a user you just have to call the ``trace_to_string``
/// function to print the trace. For more usage information
/// see the documentation below.

(*** Print Functions for Basic DY* Types ***)

val label_to_string: (l:label) -> string
let rec label_to_string l =
  match l with
  | Secret -> "Secret"
  | State pre_label -> (
    match pre_label with
    | P p -> Printf.sprintf "Principal %s" p
    | S p s -> Printf.sprintf "Principal %s state %d" p s
  ) 
  | Meet l1 l2 -> Printf.sprintf "Meet [%s; %s]" (label_to_string l1) (label_to_string l2)
  | Join l1 l2 -> Printf.sprintf "Join [%s; %s]" (label_to_string l1) (label_to_string l2)
  | Public -> "Public"

val usage_to_string: (u:usage) -> string
let usage_to_string u =
  match u with
  | SigKey tag -> "SigKey " ^ tag
  | SigNonce -> "SigNonce"
  | PkdecKey tag -> "PkdecKey " ^ tag
  | PkNonce -> "PkNonce"
  | AeadKey tag -> "AeadKey " ^ tag
  | DhKey tag -> "DhKey " ^ tag
  | NoUsage -> "NoUsage"

val uint_list_to_string: list FStar.UInt8.t -> string
let rec uint_list_to_string seq =
  match seq with
  | [] -> ""
  | hd :: tl -> (
    // Only convert certain ASCII characters to create clean strings
    // without special characters.
    if FStar.UInt8.gt (FStar.UInt8.uint_to_t 32) hd || FStar.UInt8.lt (FStar.UInt8.uint_to_t 122) hd then uint_list_to_string tl
    else Printf.sprintf "%c%s" (FStar.Char.char_of_int (FStar.UInt8.v hd)) (uint_list_to_string tl)
  )

val bytes_to_string: (b:bytes) -> string
let rec bytes_to_string b =
  match b with
  | Literal s -> uint_list_to_string (FStar.Seq.seq_to_list s)
  
  | Rand usage label len time -> Printf.sprintf "Nonce #%d" time
  
  | Concat (Literal s) right -> (
      Printf.sprintf "%s%s" 
        (uint_list_to_string (FStar.Seq.seq_to_list s)) (bytes_to_string right)
  )
  | Concat left right -> (
    Printf.sprintf "[%s,%s]" (bytes_to_string left) (bytes_to_string right)
  )
  
  | AeadEnc key nonce msg ad -> (
    Printf.sprintf "AeadEnc(key=(%s), nonce=(%s), msg=(%s), ad=(%s))" 
      (bytes_to_string key) (bytes_to_string nonce) (bytes_to_string msg)
      (bytes_to_string ad)
  )
  
  | Pk sk -> Printf.sprintf "Pk(sk=(%s))" (bytes_to_string sk)
  | PkEnc pk nonce msg -> (
    Printf.sprintf "PkEnc(pk=(%s), nonce=(%s), msg=(%s))" 
      (bytes_to_string pk) (bytes_to_string nonce) (bytes_to_string msg)
  )
  
  | Vk sk -> Printf.sprintf "Public Key (%s)" (bytes_to_string sk)
  | Sign sk nonce msg -> (
    Printf.sprintf "sig(sk=(%s), nonce=(%s), msg=(%s))" 
      (bytes_to_string sk) (bytes_to_string nonce) (bytes_to_string msg)
  )

  | Hash msg -> Printf.sprintf "Hash(%s)" (bytes_to_string msg)

  | DhPub sk -> Printf.sprintf "DhPub(sk=(%s))" (bytes_to_string sk)
  | Dh sk pk -> (
    Printf.sprintf "Dh(sk=(%s), pk=(%s))" (bytes_to_string sk) (bytes_to_string pk)
  )

(*** State Parsing Helper Functions ***)

val get_state_content: bytes -> bytes
let get_state_content full_content_bytes =
  let full_content = parse session full_content_bytes in
  match full_content with
  | Some ({label; content}) -> content
  | None -> full_content_bytes

/// This section uses fully qualified names
/// for some types because they are defined
/// in DY.Lib and DY.Core. This causes
/// conflicts with the bytes_to_string function.

val private_key_type_to_string: DY.Lib.State.PrivateKeys.private_key_type -> string
let private_key_type_to_string t =
  match t with
  | DY.Lib.State.PrivateKeys.PkDec u -> "PkDec " ^ u
  | DY.Lib.State.PrivateKeys.Sign u -> "Sign " ^ u

val private_keys_types_to_string: (list (map_elem DY.Lib.State.PrivateKeys.private_keys_types)) -> string
let rec private_keys_types_to_string m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (private_keys_types_to_string tl) ^ 
    Printf.sprintf "%s = (%s)," (private_key_type_to_string hd.key) (bytes_to_string hd.value.private_key)
  )

val public_key_type_to_string: DY.Lib.State.PKI.public_key_type -> string
let public_key_type_to_string t =
  match t with
  | DY.Lib.State.PKI.PkEnc u -> "PkEnc " ^ u
  | DY.Lib.State.PKI.Verify u -> "Verify " ^ u

val pki_types_to_string: (list (map_elem DY.Lib.State.PKI.pki_types)) -> string
let rec pki_types_to_string m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (pki_types_to_string tl) ^ 
    Printf.sprintf "%s [%s] = (%s)," (public_key_type_to_string hd.key.ty) hd.key.who (bytes_to_string hd.value.public_key)
  )

/// This function converts the states containing
/// private and public keys to nicely looking strings.
/// If it is not such a state the function calls the
/// user provided state parsing function. If that function
/// also fails it calls the bytes_to_string function
/// as a fallback.

val state_to_str_helper: (bytes -> option string) -> bytes ->  string
let state_to_str_helper state_to_str sess_bytes =
  let sess = parse (map DY.Lib.State.PrivateKeys.private_keys_types) sess_bytes in
  match sess with
  | Some m -> Printf.sprintf "[%s]" (private_keys_types_to_string m.key_values)
  | None -> (
    let sess = parse (map DY.Lib.State.PKI.pki_types) sess_bytes in
    match sess with
    | Some m -> Printf.sprintf "[%s]" (pki_types_to_string m.key_values)
    | None -> (
      let str = state_to_str sess_bytes in
      match str with
      | Some s -> s
      | None -> (bytes_to_string sess_bytes)
    )
  )


(*** Functions to Print the Trace ***)

val option_to_str: (bytes -> option string) -> bytes -> string
let option_to_str parse_fn elem =
  let parsed = parse_fn elem in
  match parsed with
  | Some str -> str
  | None -> bytes_to_string elem // Parse bytes with the default method as a fallback

val trace_event_to_string: 
  trace_event -> nat -> 
  (bytes -> option string) -> (bytes -> option string) -> (bytes -> option string) -> 
  string
let trace_event_to_string tr_event i message_to_str state_to_str event_to_str =
  match tr_event with
  | MsgSent msg -> (
    let msg_str = option_to_str message_to_str msg in
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Message\", \"Content\": \"%s\"}\n"
      i msg_str
  )
  | RandGen usg lab len -> (
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Nonce\", \"Usage\": \"%s\", \"Label\": \"%s\"}\n" 
    i (usage_to_string usg) (label_to_string lab)
  )
  | Corrupt prin sess_id -> ""
  | SetState prin sess_id full_content -> (
    let content = get_state_content full_content in
    let content_str = state_to_str_helper state_to_str content in
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Session\", \"SessionID\": %d, \"Principal\": \"%s\", \"Content\": \"%s\"}\n"
      i sess_id prin content_str
  )
  | Event prin tag content -> (
    let content_str = option_to_str event_to_str content in
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Event\", \"Principal\": \"%s\", \"Tag\": \"%s\", \"Content\": \"%s\"}\n" 
      i prin tag content_str
  )

/// Helper function for `trace_to_string` to avoid calling `length` for each trace event,
/// which would lead to quadratic complexity.

val trace_to_string_helper:
  (tr:trace) -> (i:nat{i = DY.Core.Trace.Type.length tr}) ->
  (bytes -> option string) -> (bytes -> option string) -> (bytes -> option string) ->
   string
let rec trace_to_string_helper tr i message_to_str state_to_str event_to_str =
  match tr with
  | Nil -> ""
  | Snoc ptr ev -> (
      trace_to_string_helper ptr (i-1) message_to_str state_to_str event_to_str ^ 
      trace_event_to_string ev i message_to_str state_to_str event_to_str
  )

(*** Functions for Users ***)

/// This method can be used to print the trace of
/// an example protocol run to the console.
/// The output can be parsed and converted to a
/// Plantuml sequence diagram with the following
/// experimental Python script: https://github.com/fabian-hk/dolev-yao-star-output-parser
///
/// Usage:
/// let* tr = get_trace in
/// let _ = IO.debug_print_string (
///           trace_to_string tr default_message_to_str default_state_to_str default_event_to_str
///         ) in

val trace_to_string: 
  trace -> 
  (bytes -> option string) -> (bytes -> option string) -> (bytes -> option string) ->
  string
let trace_to_string tr message_to_str state_to_str event_to_str =
  trace_to_string_helper tr (DY.Core.Trace.Type.length tr) message_to_str state_to_str event_to_str

val default_message_to_str: bytes -> option string
let default_message_to_str b = Some (bytes_to_string b)

val default_state_to_str: bytes -> option string
let default_state_to_str b = Some (bytes_to_string b)

val default_event_to_str: bytes -> option string
let default_event_to_str b = Some (bytes_to_string b)
