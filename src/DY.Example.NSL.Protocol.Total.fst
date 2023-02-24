module DY.Example.NSL.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

// Needham-Schroeder-Lowe Fixed Public Key Protocol [2]
//
// A -> B: {N_A, A}K_PB       msg 1
// B -> A: {N_A, N_B, B}K_PA  msg 2 -- note addition of B
// A -> B: {N_B}K_PB          msg 3
//
// [2] Gavin Lowe. "Breaking and fixing the Needham-Schroeder Public-Key
//     Protocol using FDR". TACAS, pp 147-166, 1996.
//
// Note: the version implemented in DY* has a modified msg 3:
// it is {N_B, A}K_PB

val (let?): #a:Type -> #b:Type -> x:option a -> (y:a -> Pure (option b) (requires x == Some y) (ensures fun _ -> True)) -> option b
let (let?) #a #b x f =
  match x with
  | None -> None
  | Some x -> f x

val guard: b:bool -> option unit
let guard b =
  if b then Some ()
  else None

(*** Message 1 ***)

type message1_ (bytes:Type0) {|bytes_like bytes|} = {
  n_a: bytes;
  alice: principal;
}

%splice [ps_message1_] (gen_parser (`message1_))
%splice [ps_message1__is_well_formed] (gen_is_well_formed_lemma (`message1_))

type message2_ (bytes:Type0) {|bytes_like bytes|} = {
  n_a: bytes;
  n_b: bytes;
  bob: principal;
}

%splice [ps_message2_] (gen_parser (`message2_))
%splice [ps_message2__is_well_formed] (gen_is_well_formed_lemma (`message2_))

type message3_ (bytes:Type0) {|bytes_like bytes|} = {
  n_b: bytes;
  // The `alice` principal is an addition of DY* example
  alice: principal;
}

%splice [ps_message3_] (gen_parser (`message3_))
%splice [ps_message3__is_well_formed] (gen_is_well_formed_lemma (`message3_))

type message_ (bytes:Type0) {|bytes_like bytes|} =
  | Msg1: message1_ bytes -> message_ bytes
  | Msg2: message2_ bytes -> message_ bytes
  | Msg3: message3_ bytes -> message_ bytes

%splice [ps_message_] (gen_parser (`message_))
%splice [ps_message__is_well_formed] (gen_is_well_formed_lemma (`message_))

instance parseable_serializeable_message_ (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (message_ bytes) = mk_parseable_serializeable (ps_message_)

type message = message_ bytes
type message1 = message1_ bytes
type message2 = message2_ bytes
type message3 = message3_ bytes

val compute_message1: principal -> principal -> bytes -> bytes -> bytes -> bytes
let compute_message1 alice bob pk_b n_a nonce =
  let msg = Msg1 {n_a; alice;} in
  pk_enc pk_b nonce (serialize message msg)

val decode_message1: principal -> bytes -> bytes -> option message1
let decode_message1 bob msg1_cipher sk_b =
  let? msg1_plain = pk_dec sk_b msg1_cipher in
  let? msg1 = parse message msg1_plain in
  guard (Msg1? msg1);?
  Some (Msg1?._0 msg1)

(*** Message 2 ***)

val compute_message2: principal -> message1 -> bytes -> bytes -> bytes -> bytes
let compute_message2 bob msg1 pk_a n_b nonce =
  let msg2 = Msg2 {n_a = msg1.n_a;  n_b; bob;} in
  pk_enc pk_a nonce (serialize message msg2)

val decode_message2: principal -> principal -> bytes -> bytes -> bytes -> option (message2)
let decode_message2 alice bob msg2_cipher sk_a n_a =
  let? msg2_plain = pk_dec sk_a msg2_cipher in
  let? msg2 = parse _ msg2_plain in
  guard (Msg2? msg2);?
  let (Msg2 msg2) = msg2 in
  guard (n_a = msg2.n_a);?
  guard (bob = msg2.bob);?
  Some msg2

(*** Message 3 ***)

val compute_message3: principal -> principal -> bytes -> bytes -> bytes -> bytes
let compute_message3 alice bob pk_b n_b nonce =
  let msg3 = Msg3 {n_b; alice;} in
  pk_enc pk_b nonce (serialize message msg3)

val decode_message3: principal -> principal -> bytes -> bytes -> bytes -> option (message3)
let decode_message3 alice bob msg_cipher sk_b n_b =
  let? msg_plain = pk_dec sk_b msg_cipher in
  let? msg = parse _ msg_plain in
  guard (Msg3? msg);?
  let (Msg3 msg3) = msg in
  guard (n_b = msg3.n_b);?
  guard (alice = msg3.alice);?
  Some msg3
