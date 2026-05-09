module DY.Example.BAN_CCITT_X509_3.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

(*** Message 1 ***)

[@@ with_bytes bytes]
type sig_message1 = {
  sm1_n_a: bytes;
  sm1_bob: principal;
  sm1_x_a: bytes;
  sm1_y_a_enc: bytes;
}

%splice [ps_sig_message1] (gen_parser (`sig_message1))
%splice [ps_sig_message1_is_well_formed] (gen_is_well_formed_lemma (`sig_message1))
instance parseable_serializeable_sig_message1: parseable_serializeable bytes sig_message1 = mk_parseable_serializeable ps_sig_message1

[@@ with_bytes bytes]
type message1 = {
  m1_alice: principal;
  m1_n_a: bytes;
  m1_bob: principal;
  m1_x_a: bytes;
  m1_y_a_enc: bytes;
  m1_sg: bytes;
}

%splice [ps_message1] (gen_parser (`message1))
%splice [ps_message1_is_well_formed] (gen_is_well_formed_lemma (`message1))
instance parseable_serializeable_message1: parseable_serializeable bytes message1 = mk_parseable_serializeable ps_message1

(*** Message 2 ***)

[@@ with_bytes bytes]
type sig_message2 = {
  sm2_n_b: bytes;
  sm2_alice: principal;
  sm2_n_a: bytes;
  sm2_x_b: bytes;
  sm2_y_b_enc: bytes;
}

%splice [ps_sig_message2] (gen_parser (`sig_message2))
%splice [ps_sig_message2_is_well_formed] (gen_is_well_formed_lemma (`sig_message2))
instance parseable_serializeable_sig_message2: parseable_serializeable bytes sig_message2 = mk_parseable_serializeable ps_sig_message2

[@@ with_bytes bytes]
type message2 = {
  m2_bob: principal;
  m2_n_b: bytes;
  m2_alice: principal;
  m2_n_a: bytes;
  m2_x_b: bytes;
  m2_y_b_enc: bytes;
  m2_sg: bytes;
}

%splice [ps_message2] (gen_parser (`message2))
%splice [ps_message2_is_well_formed] (gen_is_well_formed_lemma (`message2))
instance parseable_serializeable_message2: parseable_serializeable bytes message2 = mk_parseable_serializeable ps_message2

(*** Message 3 ***)

[@@ with_bytes bytes]
type sig_message3 = {
  sm3_bob: principal;
  sm3_n_b: bytes;
}

%splice [ps_sig_message3] (gen_parser (`sig_message3))
%splice [ps_sig_message3_is_well_formed] (gen_is_well_formed_lemma (`sig_message3))
instance parseable_serializeable_sig_message3: parseable_serializeable bytes sig_message3 = mk_parseable_serializeable ps_sig_message3

[@@ with_bytes bytes]
type message3 = {
  m3_alice: principal;
  m3_bob: principal;
  m3_n_b: bytes;
  m3_sg: bytes;
}

%splice [ps_message3] (gen_parser (`message3))
%splice [ps_message3_is_well_formed] (gen_is_well_formed_lemma (`message3))
instance parseable_serializeable_message3: parseable_serializeable bytes message3 = mk_parseable_serializeable ps_message3

(*** Global message type ***)

[@@ with_bytes bytes]
type message =
  | Msg1: message1 -> message
  | Msg2: message2 -> message
  | Msg3: message3 -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message

instance parseable_serializeable_principal: parseable_serializeable bytes principal = mk_parseable_serializeable ps_principal

(*** Tagged signed payload (union) ***)

[@@ with_bytes bytes]
type sig_message =
  | SigMsg1: sig_message1 -> sig_message
  | SigMsg2: sig_message2 -> sig_message
  | SigMsg3: sig_message3 -> sig_message

%splice [ps_sig_message] (gen_parser (`sig_message))
%splice [ps_sig_message_is_well_formed] (gen_is_well_formed_lemma (`sig_message))

instance parseable_serializeable_bytes_sig_message: parseable_serializeable bytes sig_message = mk_parseable_serializeable ps_sig_message

(*** Userdata for Ya and Yb ***)

[@@ with_bytes bytes]
type userdata = {
  data: bytes;
}

%splice [ps_userdata] (gen_parser (`userdata))
%splice [ps_userdata_is_well_formed] (gen_is_well_formed_lemma (`userdata))

instance parseable_serializeable_bytes_userdata: parseable_serializeable bytes userdata = mk_parseable_serializeable ps_userdata

(*** Processing functions ***)

[@@"opaque_to_smt"]
val compute_message1: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes
let compute_message1 alice bob pk_b n_a x_a y_a pke_nonce sig_nonce sk_a =
  let y_a_enc = pke_enc pk_b pke_nonce (serialize userdata {data=y_a}) in
  let signed_part = { sm1_n_a = n_a; sm1_bob = bob; sm1_x_a = x_a; sm1_y_a_enc = y_a_enc } in
  let sg = sign sk_a sig_nonce (serialize sig_message (SigMsg1 signed_part)) in
  serialize message (Msg1 { m1_alice = alice; m1_n_a = n_a; m1_bob = bob; m1_x_a = x_a; m1_y_a_enc = y_a_enc; m1_sg = sg })

[@@"opaque_to_smt"]
val decode_message1: bytes -> principal -> bytes -> option message1
let decode_message1 msg1_bytes bob vk_a =
  let? msg = parse message msg1_bytes in
  guard (Msg1? msg);?
  let msg1 = Msg1?._0 msg in
  guard (msg1.m1_bob = bob);?
  let signed_part = { sm1_n_a = msg1.m1_n_a; sm1_bob = msg1.m1_bob; sm1_x_a = msg1.m1_x_a; sm1_y_a_enc = msg1.m1_y_a_enc } in
  guard (verify vk_a (serialize sig_message (SigMsg1 signed_part)) msg1.m1_sg);?
  Some msg1

[@@"opaque_to_smt"]
val compute_message2: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes
let compute_message2 bob alice pk_a n_b n_a x_b y_b pke_nonce sig_nonce sk_b =
  let y_b_enc = pke_enc pk_a pke_nonce (serialize userdata {data=y_b}) in
  let signed_part = { sm2_n_b = n_b; sm2_alice = alice; sm2_n_a = n_a; sm2_x_b = x_b; sm2_y_b_enc = y_b_enc } in
  let sg = sign sk_b sig_nonce (serialize sig_message (SigMsg2 signed_part)) in
  serialize message (Msg2 { m2_bob = bob; m2_n_b = n_b; m2_alice = alice; m2_n_a = n_a; m2_x_b = x_b; m2_y_b_enc = y_b_enc; m2_sg = sg })

[@@"opaque_to_smt"]
val decode_message2: bytes -> principal -> bytes -> bytes -> option message2
let decode_message2 msg2_bytes alice vk_b n_a =
  let? msg = parse message msg2_bytes in
  guard (Msg2? msg);?
  let msg2 = Msg2?._0 msg in
  guard (msg2.m2_alice = alice);?
  guard (msg2.m2_n_a = n_a);?
  let signed_part = { sm2_n_b = msg2.m2_n_b; sm2_alice = msg2.m2_alice; sm2_n_a = msg2.m2_n_a; sm2_x_b = msg2.m2_x_b; sm2_y_b_enc = msg2.m2_y_b_enc } in
  guard (verify vk_b (serialize sig_message (SigMsg2 signed_part)) msg2.m2_sg);?
  Some msg2

[@@"opaque_to_smt"]
val compute_message3: principal -> principal -> bytes -> bytes -> bytes -> bytes
let compute_message3 alice bob n_b sig_nonce sk_a =
  let signed_part = { sm3_bob = bob; sm3_n_b = n_b } in
  let sg = sign sk_a sig_nonce (serialize sig_message (SigMsg3 signed_part)) in
  serialize message (Msg3 { m3_alice = alice; m3_bob = bob; m3_n_b = n_b; m3_sg = sg })

[@@"opaque_to_smt"]
val decode_message3: bytes -> principal -> bytes -> bytes -> option message3
let decode_message3 msg3_bytes bob vk_a n_b =
  let? msg = parse message msg3_bytes in
  guard (Msg3? msg);?
  let msg3 = Msg3?._0 msg in
  guard (msg3.m3_bob = bob);?
  guard (msg3.m3_n_b = n_b);?
  let signed_part = { sm3_bob = msg3.m3_bob; sm3_n_b = msg3.m3_n_b } in
  guard (verify vk_a (serialize sig_message (SigMsg3 signed_part)) msg3.m3_sg);?
  Some msg3

[@@"opaque_to_smt"]
val decode_y: bytes -> bytes -> option bytes
let decode_y y_enc sk =
  let? y_plain = pke_dec sk y_enc in
  let? y_struct = parse userdata y_plain in
  Some y_struct.data
