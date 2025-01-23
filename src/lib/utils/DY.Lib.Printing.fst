module DY.Lib.Printing

open Comparse
open DY.Core
open DY.Lib.State.Tagged
open DY.Lib.State.Map

/// This module provides functions to convert types
/// from DY* to a string. These functions are used to
/// print the trace from an example protocol run.
///
/// As a user you just have to call the ``trace_to_string``
/// function to print the trace. For more usage information
/// see the documentation below.

(*** Print Functions for Basic DY* Types ***)

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
  
  | Rand len time -> Printf.sprintf "Nonce #%d" time
  
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
  | PkeEnc pk nonce msg -> (
    Printf.sprintf "PkeEnc(pk=(%s), nonce=(%s), msg=(%s))" 
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
  | KdfExtract salt ikm ->
    Printf.sprintf "KdfExtract(salt=(%s), ikm=(%s))" (bytes_to_string salt) (bytes_to_string ikm)
  | KdfExpand prk info len ->
    Printf.sprintf "KdfExpand(prk=(%s), info=(%s), len=(%d))" (bytes_to_string prk) (bytes_to_string info) len
  | KemPub sk ->
    Printf.sprintf "KemKey(sk=(%s))" (bytes_to_string sk)
  | KemEncap pk nonce ->
    Printf.sprintf "KemEncap(pk=(%s), nonce=(%s))" (bytes_to_string pk) (bytes_to_string nonce)
  | KemSecretShared nonce ->
    Printf.sprintf "KemSecretShared(nonce=(%s))" (bytes_to_string nonce)

val usage_to_string: (u:usage) -> string
let rec usage_to_string u =
  match u with
  | NoUsage -> "{\"Type\": \"NoUsage\"}"
  | SigKey tag data ->
    Printf.sprintf "{\"Type\": \"SigKey\", \"Tag\": \"%s\", \"Data\": \"%s\"}"
      tag (bytes_to_string data)
  | SigNonce -> "{\"Type\": \"SigNonce\"}"
  | PkeKey tag data ->
    Printf.sprintf "{\"Type\": \"PkeKey\", \"Tag\": \"%s\", \"Data\": \"%s\"}"
      tag (bytes_to_string data)
  | PkeNonce -> "{\"Type\": \"PkeNonce\"}"
  | AeadKey tag data ->
    Printf.sprintf "{\"Type\": \"AeadKey\", \"Tag\": \"%s\", \"Data\": \"%s\"}"
      tag (bytes_to_string data)
  | DhKey tag data ->
    Printf.sprintf "{\"Type\": \"DhKey\", \"Tag\": \"%s\", \"Data\": \"%s\"}"
      tag (bytes_to_string data)
  | KdfExpandKey tag data ->
    Printf.sprintf "{\"Type\": \"KdfExpandKey\", \"Tag\": \"%s\", \"Data\": \"%s\"}" 
      tag (bytes_to_string data)
  | KemKey usg ->
    Printf.sprintf "{\"Type\": \"KemKey\", \"Usage\": \"%s\"}" (usage_to_string usg)
  | KemNonce usg ->
    Printf.sprintf "{\"Type\": \"KemNonce\", \"Usage\": \"%s\"}" (usage_to_string usg)


(*** State Parsing Helper Functions ***)

/// This section uses fully qualified names
/// for some types because they are defined
/// in DY.Lib and DY.Core. This causes
/// conflicts with the bytes_to_string function.

val long_term_key_type_to_string: DY.Lib.State.PrivateKeys.long_term_key_type -> string
let long_term_key_type_to_string t =
  match t with
  | DY.Lib.State.PrivateKeys.LongTermPkeKey u -> "LongTermPkeKey " ^ u
  | DY.Lib.State.PrivateKeys.LongTermSigKey u -> "LongTermSigKey " ^ u

val private_keys_types_to_string: (list (map_elem DY.Lib.State.PrivateKeys.private_key_key DY.Lib.State.PrivateKeys.private_key_value)) -> string
let rec private_keys_types_to_string m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (private_keys_types_to_string tl) ^ 
    Printf.sprintf "%s = (%s)," (long_term_key_type_to_string hd.key.ty) (bytes_to_string hd.value.private_key)
  )

val pki_types_to_string: (list (map_elem DY.Lib.State.PKI.pki_key DY.Lib.State.PKI.pki_value)) -> string
let rec pki_types_to_string m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (pki_types_to_string tl) ^ 
    Printf.sprintf "%s [%s] = (%s)," (long_term_key_type_to_string hd.key.ty) hd.key.who (bytes_to_string hd.value.public_key)
  )

val default_private_keys_state_to_string: bytes -> option string
let default_private_keys_state_to_string content_bytes =
  let? state = parse (map DY.Lib.State.PrivateKeys.private_key_key DY.Lib.State.PrivateKeys.private_key_value) content_bytes in
  Some (Printf.sprintf "[%s]" (private_keys_types_to_string state.key_values))

val default_pki_state_to_string: bytes -> option string
let default_pki_state_to_string content_bytes =
  let? state = parse (map DY.Lib.State.PKI.pki_key DY.Lib.State.PKI.pki_value) content_bytes in
  Some (Printf.sprintf "[%s]" (pki_types_to_string state.key_values))

/// Searches for a printer with the correct tag
/// and returns the first one it finds.

val find_printer: list (string & (bytes -> option string)) -> string -> (bytes -> option string)
let rec find_printer printer_list tag =
  match printer_list with
  | [] -> (fun b -> Some (bytes_to_string b))
  | (parser_tag, parser) :: tl -> (
    if parser_tag = tag then parser
    else find_printer tl tag
  )

val option_to_string: (bytes -> option string) -> bytes -> string
let option_to_string parse_fn elem =
  let parsed = parse_fn elem in
  match parsed with
  | Some str -> str
  | None -> bytes_to_string elem // Parse bytes with the default method as a fallback

val state_to_string: list (string & (bytes -> option string)) -> bytes -> (string & string)
let state_to_string printer_list full_content_bytes =
  let full_content = parse tagged_state full_content_bytes in
  match full_content with
  | Some ({tag; content}) -> (
    let parser = find_printer printer_list tag in
    tag, option_to_string parser content
  )
  | None -> "Unknown Tag", bytes_to_string full_content_bytes


(*** Record to Combine All Printer Functions ***)

noeq type trace_to_string_printers = {
  message_to_string:(bytes -> option string);
  state_to_string:(list (string & (bytes -> option string)));
  event_to_string:(list (string & (bytes -> option string)))
}


(*** Functions to Print the Trace ***)

val trace_entry_to_string: 
  trace_to_string_printers -> 
  trace_entry -> timestamp -> 
  string
let trace_entry_to_string printers tr_entry i =
  match tr_entry with
  | MsgSent msg -> (
    let msg_str = option_to_string printers.message_to_string msg in
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Message\", \"Content\": \"%s\"}\n"
      (i-1) msg_str
  )
  | RandGen usg lab len -> (
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Nonce\", \"Usage\": %s}\n" 
      (i-1) (usage_to_string usg)
  )
  | Corrupt time -> ""
  | SetState prin sess_id full_content -> (
    let tag, content_str = state_to_string printers.state_to_string full_content in
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Session\", \"SessionID\": %d, \"Principal\": \"%s\", \"Tag\": \"%s\", \"Content\": \"%s\"}\n"
      (i-1) sess_id.the_id prin tag content_str
  )
  | Event prin tag content -> (
    let printer = find_printer printers.event_to_string tag in
    let content_str = option_to_string printer content in
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Event\", \"Principal\": \"%s\", \"Tag\": \"%s\", \"Content\": \"%s\"}\n" 
      (i-1) prin tag content_str
  )

/// Helper function for `trace_to_string` to avoid calling `length` for each trace entry,
/// which would lead to quadratic complexity.

val trace_to_string_helper:
  trace_to_string_printers ->
  (tr:trace) -> (i:nat{i = trace_length tr}) ->
  string
let rec trace_to_string_helper printers tr i =
  match tr with
  | Nil -> ""
  | Snoc ptr entry -> (
      trace_to_string_helper printers ptr (i-1) ^ trace_entry_to_string printers entry i
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
/// let _ = IO.debug_print_string (trace_to_string tr default_trace_to_string_printers) in

val trace_to_string: trace_to_string_printers -> trace -> string
let trace_to_string printers tr =
  trace_to_string_helper printers tr (trace_length tr)


(*** Helper Functions to Setup the Printer Functions Record ***)

val default_message_to_string: bytes -> option string
let default_message_to_string b = Some (bytes_to_string b)

val default_state_to_string: list (string & (bytes -> option string))
let default_state_to_string = []

val default_event_to_string: list (string & (bytes -> option string))
let default_event_to_string = []

val trace_to_string_printers_builder:
  (bytes -> option string) ->
  list (string & (bytes -> option string)) ->
  list (string & (bytes -> option string)) ->
  trace_to_string_printers
let trace_to_string_printers_builder message_to_string state_to_string event_to_string =
  {
    message_to_string = message_to_string;
    state_to_string = (
      List.append state_to_string (
        [
          (DY.Lib.State.PrivateKeys.map_types_private_keys.tag, default_private_keys_state_to_string);
          (DY.Lib.State.PKI.map_types_pki.tag, default_pki_state_to_string)
        ]
      ) // User supplied functions will override the default functions because the
        // find printer function will choose the first match.
    );
    event_to_string = event_to_string
  }

val default_trace_to_string_printers: trace_to_string_printers
let default_trace_to_string_printers = 
  trace_to_string_printers_builder default_message_to_string default_state_to_string default_event_to_string
