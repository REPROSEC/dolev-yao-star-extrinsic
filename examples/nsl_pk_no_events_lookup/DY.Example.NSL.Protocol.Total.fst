module DY.Example.NSL.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

/// Needham-Schroeder-Lowe Fixed Public Key Protocol [1]
///
/// A -> B: {N_A, A}K_PB       msg 1
/// B -> A: {N_A, N_B, B}K_PA  msg 2 -- note addition of B
/// A -> B: {N_B}K_PB          msg 3
///
/// [1] Gavin Lowe. "Breaking and fixing the Needham-Schroeder Public-Key
///     Protocol using FDR". TACAS, pp 147-166, 1996.
///
/// This module implements the pure part of the NSL protocol.

(*** Message type ***)

/// We first define types for messages,
/// which are used as public-key encryption input.
/// We use Comparse to generate a message format for each of these.

[@@ with_bytes bytes]
type message1 = {
  n_a: bytes;
  alice: principal;
}

%splice [ps_message1] (gen_parser (`message1))
%splice [ps_message1_is_well_formed] (gen_is_well_formed_lemma (`message1))

[@@ with_bytes bytes]
type message2 = {
  n_a: bytes;
  n_b: bytes;
  bob: principal;
}

%splice [ps_message2] (gen_parser (`message2))
%splice [ps_message2_is_well_formed] (gen_is_well_formed_lemma (`message2))

[@@ with_bytes bytes]
type message3 = {
  n_b: bytes;
}

%splice [ps_message3] (gen_parser (`message3))
%splice [ps_message3_is_well_formed] (gen_is_well_formed_lemma (`message3))

/// The type for messages.
/// This corresponds to a tagged union,
/// the tag is necessary to avoid type-confusion attacks, see [2].
///
/// [2] Catherine A. Meadows. "Analyzing the Needham-Schroeder public key protocol:
///     A comparison of two approaches". ESORICS, pages 351–364, 1996.

[@@ with_bytes bytes]
type message =
  | Msg1: message1 -> message
  | Msg2: message2 -> message
  | Msg3: message3 -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message

(*** Message 1 ***)

/// Alice generates message 1

val compute_message1: principal -> principal -> bytes -> bytes -> bytes -> bytes
let compute_message1 alice bob pk_b n_a nonce =
  let msg = Msg1 {n_a; alice;} in
  pk_enc pk_b nonce (serialize message msg)

/// Bob process message 1

val decode_message1: principal -> bytes -> bytes -> option message1
let decode_message1 bob msg1_cipher sk_b =
  let? msg1_plain = pk_dec sk_b msg1_cipher in
  let? msg1 = parse message msg1_plain in
  guard (Msg1? msg1);?
  Some (Msg1?._0 msg1)

(*** Message 2 ***)

/// Bob generates message 2

val compute_message2: principal -> message1 -> bytes -> bytes -> bytes -> bytes
let compute_message2 bob msg1 pk_a n_b nonce =
  let msg2 = Msg2 {n_a = msg1.n_a;  n_b; bob;} in
  pk_enc pk_a nonce (serialize message msg2)

/// Alice process message 2

val decode_message2: principal -> principal -> bytes -> bytes -> bytes -> option (message2)
let decode_message2 alice bob msg2_cipher sk_a n_a =
  let? msg2_plain = pk_dec sk_a msg2_cipher in
  let? msg2 = parse _ msg2_plain in
  guard (Msg2? msg2);?
  let (Msg2 msg2) = msg2 in
  guard (n_a = msg2.n_a);?
  guard (bob = msg2.bob);?
  Some msg2


val decode_message2_: principal  -> bytes -> bytes -> option (message2)
let decode_message2_ alice msg2_cipher sk_a =
  let? msg2_plain = pk_dec sk_a msg2_cipher in
  let? msg2 = parse _ msg2_plain in
  guard (Msg2? msg2);?
  let (Msg2 msg2) = msg2 in
  Some msg2

(*** Message 3 ***)

/// Alice generates message 3

val compute_message3: principal -> principal -> bytes -> bytes -> bytes -> bytes
let compute_message3 alice bob pk_b n_b nonce =
  let msg3 = Msg3 {n_b;} in
  pk_enc pk_b nonce (serialize message msg3)

/// Bob process message 3

val decode_message3: principal -> principal -> bytes -> bytes -> bytes -> option (message3)
let decode_message3 alice bob msg_cipher sk_b n_b =
  let? msg_plain = pk_dec sk_b msg_cipher in
  let? msg = parse _ msg_plain in
  guard (Msg3? msg);?
  let (Msg3 msg3) = msg in
  guard (n_b = msg3.n_b);?
  Some msg3

val decode_message3_: bytes -> bytes -> option (message3)
let decode_message3_ msg_cipher sk_b =
  let? msg_plain = pk_dec sk_b msg_cipher in
  let? msg = parse _ msg_plain in
  guard (Msg3? msg);?
  let (Msg3 msg3) = msg in
  Some msg3
