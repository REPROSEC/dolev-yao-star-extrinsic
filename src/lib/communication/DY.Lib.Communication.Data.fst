module DY.Lib.Communication.Data

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Messages ***)

(**** Core ****)

/// The following type is meant to be used to send a single byte with a function
/// of the communication layer. Since the communication layer always takes a
/// serializable data object we need to encapsulate the byte in a data object.
[@@with_bytes bytes]
type com_send_byte = {
  b:bytes;
}

%splice [ps_com_send_byte] (gen_parser (`com_send_byte))
%splice [ps_com_send_byte_is_well_formed] (gen_is_well_formed_lemma (`com_send_byte))

instance parseable_serializeable_bytes_com_send_byte: parseable_serializeable bytes com_send_byte
  = mk_parseable_serializeable ps_com_send_byte

/// Data structure to return data from communication layer functions
type communication_message (a:Type) = {
  sender:principal;
  receiver:principal;  
  payload:a;
}

[@@with_bytes bytes]
type signature_input = 
  | Plain: sender:principal -> receiver:principal -> payload:bytes -> signature_input
  | Encrypted: sender:principal -> receiver:principal -> payload:bytes -> pk:bytes -> signature_input

#push-options "--ifuel 1 --fuel 0"
%splice [ps_signature_input] (gen_parser (`signature_input))
%splice [ps_signature_input_is_well_formed] (gen_is_well_formed_lemma (`signature_input))
#pop-options

instance parseable_serializeable_bytes_signature_input: parseable_serializeable bytes signature_input
  = mk_parseable_serializeable ps_signature_input

[@@with_bytes bytes]
type signed_communication_message = {
  msg:bytes;
  signature:bytes;
}

%splice [ps_signed_communication_message] (gen_parser (`signed_communication_message))
%splice [ps_signed_communication_message_is_well_formed] (gen_is_well_formed_lemma (`signed_communication_message))

(**** Request/Response ****)

[@@with_bytes bytes]
type request_message = {
  request:bytes;
  key:bytes
}

%splice [ps_request_message] (gen_parser (`request_message))
%splice [ps_request_message_is_well_formed] (gen_is_well_formed_lemma (`request_message))

[@@with_bytes bytes]
type response_envelope = {
  nonce:bytes;
  ciphertext:bytes
}

%splice [ps_response_envelope] (gen_parser (`response_envelope))
%splice [ps_response_envelope_is_well_formed] (gen_is_well_formed_lemma (`response_envelope))

[@@with_bytes bytes]
type authenticated_data = {
  server:principal
}

%splice [ps_authenticated_data] (gen_parser (`authenticated_data))
%splice [ps_authenticated_data_is_well_formed] (gen_is_well_formed_lemma (`authenticated_data))

instance parseable_serializeable_bytes_authenticated_data: parseable_serializeable bytes authenticated_data
  = mk_parseable_serializeable ps_authenticated_data


(**** Message Type for all Messages on the Wire ****)

[@@with_bytes bytes]
type com_message_t =
  | SigMessage: signed_communication_message -> com_message_t
  | RequestMessage: request_message -> com_message_t
  | ResponseMessage: response_envelope -> com_message_t

#push-options "--ifuel 1"
%splice [ps_com_message_t] (gen_parser (`com_message_t))
%splice [ps_com_message_t_is_well_formed] (gen_is_well_formed_lemma (`com_message_t))
#pop-options

instance parseable_serializeable_bytes_com_message_t: parseable_serializeable bytes com_message_t
  = mk_parseable_serializeable ps_com_message_t
