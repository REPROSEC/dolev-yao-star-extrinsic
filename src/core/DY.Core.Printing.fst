module DY.Core.Printing

open DY.Core.Trace.Type
open DY.Core.Label.Type
open DY.Core.Bytes.Type

/// This module provides functions to convert types
/// from DY* to a string. These functions are used to
/// print the trace from an example protocol run.

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
  
  | Concat (Literal s) right -> Printf.sprintf "%s%s" 
                                  (uint_list_to_string (FStar.Seq.seq_to_list s)) (bytes_to_string right)
  | Concat left right -> Printf.sprintf "[%s,%s]" (bytes_to_string left) (bytes_to_string right)
  
  | AeadEnc key nonce msg ad -> Printf.sprintf "AeadEnc(key=(%s), nonce=(%s), msg=(%s), ad=(%s))" 
                              (bytes_to_string key) (bytes_to_string nonce) (bytes_to_string msg)
                              (bytes_to_string ad)
  
  | Pk sk -> Printf.sprintf "Pk(sk=(%s))" (bytes_to_string sk)
  | PkEnc pk nonce msg -> Printf.sprintf "PkEnc(pk=(%s), nonce=(%s), msg=(%s))" 
                              (bytes_to_string pk) (bytes_to_string nonce) (bytes_to_string msg)
  
  | Vk sk -> Printf.sprintf "Public Key (%s)" (bytes_to_string sk)
  | Sign sk nonce msg -> Printf.sprintf "sig(sk=(%s), nonce=(%s), msg=(%s))" 
                              (bytes_to_string sk) (bytes_to_string nonce) (bytes_to_string msg)

  | Hash msg -> Printf.sprintf "Hash(%s)" (bytes_to_string msg)

  | DhPub sk -> Printf.sprintf "DhPub(sk=(%s))" (bytes_to_string sk)
  | Dh sk pk -> Printf.sprintf "Dh(sk=(%s), pk=(%s))" (bytes_to_string sk) (bytes_to_string pk)

val trace_event_to_string: trace_event -> nat -> string
let trace_event_to_string tr_event i =
  match tr_event with
  | MsgSent msg -> (
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Message\", \"Content\": \"%s\"}\n"
      i (bytes_to_string msg)
  )
  | RandGen usg lab len -> (
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Nonce\", \"Usage\": \"%s\", \"Label\": \"%s\"}\n" 
    i (usage_to_string usg) (label_to_string lab)
  )
  | Corrupt prin sess_id -> ""
  | SetState prin sess_id content -> (
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Session\", \"SessionID\": %d, \"Principal\": \"%s\", \"Content\": \"%s\"}\n"
      i sess_id prin (bytes_to_string content)
  )
  | Event prin tag content -> (
    Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Event\", \"Principal\": \"%s\", \"Tag\": \"%s\", \"Content\": \"%s\"}\n" 
      i prin tag (bytes_to_string content)
  )

val trace_to_string_helper: (tr:trace) -> (i:nat{i = length tr}) -> string
let rec trace_to_string_helper tr i =
  match tr with
  | Nil -> ""
  | Snoc ptr ev -> trace_to_string_helper ptr (i-1) ^ trace_event_to_string ev i

/// This method can be used to print the trace of
/// an example protocol run to the console.
/// The output can be parsed and converted to a
/// Plantuml sequence diagram with the following
/// experimental Python script: https://github.com/fabian-hk/dolev-yao-star-output-parser
///
/// Usage:
/// let* tr = get_trace in
/// let _ = IO.debug_print_string (trace_to_string tr) in

val trace_to_string: trace -> string
let trace_to_string tr =
  trace_to_string_helper tr (length tr)