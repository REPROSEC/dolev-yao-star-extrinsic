module DY.Example.SingleMessage.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

(*
  C -> S: pkenc(pk_server, {secret})
*)

[@@with_bytes bytes]
type single_message = {
  secret:bytes;
}

%splice [ps_single_message] (gen_parser (`single_message))
%splice [ps_single_message_is_well_formed] (gen_is_well_formed_lemma (`single_message))

[@@with_bytes bytes]
type message =
  | Msg: single_message -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message
  = mk_parseable_serializeable ps_message


(*** Protocol ***)

val compute_message: bytes -> bytes
let compute_message secret =
  let msg = Msg {secret;} in
  serialize message msg

val decode_message: bytes -> option single_message
let decode_message msg_bytes =
  let? msg = parse message msg_bytes in
  guard (Msg? msg);?
  Some (Msg?._0 msg)
