module DY.Example.CCITT.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

instance parseable_serializeable_string: parseable_serializeable bytes string = mk_parseable_serializeable ps_string

(*** Message types ***)

[@@ with_bytes bytes]
type inner_payload = {
  ya: bytes;
  sig_h_ya: bytes;
}

%splice [ps_inner_payload] (gen_parser (`inner_payload))
%splice [ps_inner_payload_is_well_formed] (gen_is_well_formed_lemma (`inner_payload))

instance parseable_serializeable_inner_payload: parseable_serializeable bytes inner_payload = mk_parseable_serializeable ps_inner_payload

[@@ with_bytes bytes]
type msg1_payload = {
  ta: bytes;
  na: bytes;
  bob: principal;
  xa: bytes;
  inner_cipher: bytes;
}

%splice [ps_msg1_payload] (gen_parser (`msg1_payload))
%splice [ps_msg1_payload_is_well_formed] (gen_is_well_formed_lemma (`msg1_payload))

instance parseable_serializeable_msg1_payload: parseable_serializeable bytes msg1_payload = mk_parseable_serializeable ps_msg1_payload

/// Tagged union of signed payload variants. Using one tagged union (rather than
/// signing each variant separately) ensures the sign predicate's parse step
/// dispatches exactly one branch per byte string.

[@@ with_bytes bytes]
type sig_message =
  | SigInner: hash_of_ya:bytes -> sig_message
  | SigOuter: payload:msg1_payload -> sig_message

%splice [ps_sig_message] (gen_parser (`sig_message))
%splice [ps_sig_message_is_well_formed] (gen_is_well_formed_lemma (`sig_message))

instance parseable_serializeable_sig_message: parseable_serializeable bytes sig_message = mk_parseable_serializeable ps_sig_message

[@@ with_bytes bytes]
type message =
  | Msg1: payload:msg1_payload -> signature:bytes -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message

(*** Message 1 ***)

/// Alice generates message 1.
/// Both the inner and outer signatures wrap their payload in `sig_message`
/// so that the crypto sign predicate has a single dispatched branch per byte string.

[@@"opaque_to_smt"]
val compute_message1:
  ta:bytes -> na:bytes -> bob:principal -> xa:bytes -> ya:bytes ->
  pk_b:bytes -> sk_a:bytes ->
  n_inner_sig:bytes -> n_inner_pke:bytes -> n_outer:bytes ->
  bytes
let compute_message1 ta na bob xa ya pk_b sk_a n_inner_sig n_inner_pke n_outer =
  let h_ya = hash ya in
  let sig_h_ya = sign sk_a n_inner_sig (serialize sig_message (SigInner h_ya)) in
  let ip = { ya; sig_h_ya; } in
  let inner_cipher = pke_enc pk_b n_inner_pke (serialize inner_payload ip) in
  let payload = { ta; na; bob; xa; inner_cipher; } in
  let signature = sign sk_a n_outer (serialize sig_message (SigOuter payload)) in
  serialize message (Msg1 payload signature)

/// Bob processes message 1.

[@@"opaque_to_smt"]
val decode_message1:
  bob:principal -> msg_bytes:bytes ->
  sk_b:bytes -> vk_a:bytes ->
  option (bytes & bytes & principal & bytes & bytes)
let decode_message1 bob msg_bytes sk_b vk_a =
  let? msg = parse message msg_bytes in
  guard (Msg1? msg);?
  let Msg1 payload signature = msg in
  guard (payload.bob = bob);?
  guard (verify vk_a (serialize sig_message (SigOuter payload)) signature);?
  let? ip_bytes = pke_dec sk_b payload.inner_cipher in
  let? ip = parse inner_payload ip_bytes in
  guard (verify vk_a (serialize sig_message (SigInner (hash ip.ya))) ip.sig_h_ya);?
  Some (payload.ta, payload.na, payload.bob, payload.xa, ip.ya)
