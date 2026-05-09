module DY.Example.AndrewRPC.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

[@@ with_bytes bytes]
type andrew_rpc_key_data = {
  akd_alice: principal;
  akd_bob: principal;
}

%splice [ps_andrew_rpc_key_data] (gen_parser (`andrew_rpc_key_data))
%splice [ps_andrew_rpc_key_data_is_well_formed] (gen_is_well_formed_lemma (`andrew_rpc_key_data))

instance parseable_serializeable_andrew_rpc_key_data: parseable_serializeable bytes andrew_rpc_key_data = mk_parseable_serializeable ps_andrew_rpc_key_data

[@@ with_bytes bytes]
type andrew_rpc_session_key_data = {
  askd_alice: principal;
  askd_bob: principal;
  askd_n_a: bytes;
}

%splice [ps_andrew_rpc_session_key_data] (gen_parser (`andrew_rpc_session_key_data))
%splice [ps_andrew_rpc_session_key_data_is_well_formed] (gen_is_well_formed_lemma (`andrew_rpc_session_key_data))

instance parseable_serializeable_andrew_rpc_session_key_data: parseable_serializeable bytes andrew_rpc_session_key_data = mk_parseable_serializeable ps_andrew_rpc_session_key_data

[@@ with_bytes bytes]
type message2 = {
  m2_n_a: bytes;
  m2_k_prime_ab: bytes;
  m2_bob: principal;
}

%splice [ps_message2] (gen_parser (`message2))
%splice [ps_message2_is_well_formed] (gen_is_well_formed_lemma (`message2))

[@@ with_bytes bytes]
type message3 = {
  m3_n_a: bytes;
}

%splice [ps_message3] (gen_parser (`message3))
%splice [ps_message3_is_well_formed] (gen_is_well_formed_lemma (`message3))

[@@ with_bytes bytes]
type message =
  | Msg1: alice:principal -> n_a:bytes -> message
  | Msg2: message2 -> message
  | Msg3: message3 -> message
  | Msg4: n_b:bytes -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message

(*** Message 1 ***)
[@@ "opaque_to_smt"]
val compute_message1: principal -> bytes -> bytes
let compute_message1 alice n_a =
  serialize message (Msg1 alice n_a)

[@@ "opaque_to_smt"]
val decode_message1: bytes -> option (principal & bytes)
let decode_message1 msg_bytes =
  let? msg = parse message msg_bytes in
  guard (Msg1? msg);?
  let Msg1 alice n_a = msg in
  Some (alice, n_a)

(*** Message 2 ***)
[@@ "opaque_to_smt"]
val compute_message2: bytes -> bytes -> bytes -> bytes -> principal -> bytes
let compute_message2 kab n_a k_prime_ab nonce bob =
  let msg2 = Msg2 {m2_n_a = n_a; m2_k_prime_ab = k_prime_ab; m2_bob = bob} in
  let ad = empty in
  let ciphertext = aead_enc kab nonce (serialize message msg2) ad in
  concat nonce ciphertext

[@@ "opaque_to_smt"]
val decode_message2: bytes -> bytes -> option message2
let decode_message2 kab msg2_with_nonce =
  let? (nonce, ciphertext) = split msg2_with_nonce 12 in
  let ad = empty in
  let? msg_bytes = aead_dec kab nonce ciphertext ad in
  let? msg = parse message msg_bytes in
  guard (Msg2? msg);?
  Some (Msg2?._0 msg)

(*** Message 3 ***)
[@@ "opaque_to_smt"]
val compute_message3: bytes -> bytes -> bytes -> bytes
let compute_message3 k_prime_ab n_a nonce =
  let msg3 = Msg3 {m3_n_a = n_a} in
  let ad = empty in
  let ciphertext = aead_enc k_prime_ab nonce (serialize message msg3) ad in
  concat nonce ciphertext

[@@ "opaque_to_smt"]
val decode_message3: bytes -> bytes -> option message3
let decode_message3 k_prime_ab msg3_with_nonce =
  let? (nonce, ciphertext) = split msg3_with_nonce 12 in
  let ad = empty in
  let? msg_bytes = aead_dec k_prime_ab nonce ciphertext ad in
  let? msg = parse message msg_bytes in
  guard (Msg3? msg);?
  Some (Msg3?._0 msg)

(*** Message 4 ***)
[@@ "opaque_to_smt"]
val compute_message4: bytes -> bytes
let compute_message4 n_b =
  serialize message (Msg4 n_b)

[@@ "opaque_to_smt"]
val decode_message4: bytes -> option bytes
let decode_message4 msg_bytes =
  let? msg = parse message msg_bytes in
  guard (Msg4? msg);?
  let Msg4 n_b = msg in
  Some n_b
