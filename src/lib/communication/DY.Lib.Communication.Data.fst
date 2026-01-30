module DY.Lib.Communication.Data

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Messages ***)

(**** Core ****)

/// Communication layer core configuration
class comm_layer_core_config (a:Type) = {
  core_tag: string;
  core_ps_a: parser_serializer bytes a;
}

instance parseable_serializeable_bytes_a_core (#a:Type) {|config:comm_layer_core_config a|}: parseable_serializeable bytes a =
  mk_parseable_serializeable config.core_ps_a

/// Data structure to return data from communication layer functions
type communication_message (a:Type) = {
  sender:principal;
  receiver:principal;
  payload:a;
}

[@@with_bytes bytes]
type encryption_input (a:Type) {|config:comm_layer_core_config a|} =
  | Unsigned: [@@@ with_parser #bytes config.core_ps_a] payload:a -> encryption_input a
  | Signed: [@@@ with_parser #bytes config.core_ps_a] payload:a -> encryption_input a

#push-options "--ifuel 1 --fuel 0"
%splice [ps_encryption_input] (gen_parser (`encryption_input))
%splice [ps_encryption_input_is_well_formed] (gen_is_well_formed_lemma (`encryption_input))
#pop-options

instance parseable_serializeable_bytes_encryption_input (#a:Type) {|config:comm_layer_core_config a|}: parseable_serializeable bytes (encryption_input a)
  = mk_parseable_serializeable (ps_encryption_input a)

[@@with_bytes bytes]
type signature_input (a:Type) {|config:comm_layer_core_config a|} = 
  | Plain: sender:principal -> receiver:principal -> [@@@ with_parser #bytes config.core_ps_a] payload:a -> signature_input a
  | Encrypted: sender:principal -> receiver:principal -> payload:bytes -> pk:bytes -> signature_input a

#push-options "--ifuel 1 --fuel 0"
%splice [ps_signature_input] (gen_parser (`signature_input))
%splice [ps_signature_input_is_well_formed] (gen_is_well_formed_lemma (`signature_input))
#pop-options

instance parseable_serializeable_bytes_signature_input (#a:Type) {|config:comm_layer_core_config a|}: parseable_serializeable bytes (signature_input a)
  = mk_parseable_serializeable (ps_signature_input a)

[@@with_bytes bytes]
type signed_communication_message = {
  msg:bytes;
  signature:bytes;
}

%splice [ps_signed_communication_message] (gen_parser (`signed_communication_message))
%splice [ps_signed_communication_message_is_well_formed] (gen_is_well_formed_lemma (`signed_communication_message))

(**** Request/Response ****)

/// Communication layer reqres configuration
class comm_layer_reqres_config (a:Type) = {
  reqres_tag: string;
  reqres_ps_a: parser_serializer bytes a;
}

instance parseable_serializeable_bytes_a_reqres (#a:Type) {|config:comm_layer_reqres_config a|}: parseable_serializeable bytes a =
  mk_parseable_serializeable config.reqres_ps_a

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
type comm_message_t =
  | SigMessage: signed_communication_message -> comm_message_t
  | RequestMessage: request_message -> comm_message_t
  | ResponseMessage: response_envelope -> comm_message_t

#push-options "--ifuel 1"
%splice [ps_comm_message_t] (gen_parser (`comm_message_t))
%splice [ps_comm_message_t_is_well_formed] (gen_is_well_formed_lemma (`comm_message_t))
#pop-options

instance parseable_serializeable_bytes_comm_message_t: parseable_serializeable bytes comm_message_t
  = mk_parseable_serializeable ps_comm_message_t
