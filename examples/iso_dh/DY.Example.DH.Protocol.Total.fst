module DY.Example.DH.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

(*
 *** ISO-DH Protocol ***

 Diffie-Hellman key exchange protocol with digital signatures based on
 ISO/IEC 9798-3:2019(E): IT Security techniques — Entity authentication — Part
 3: Mechanisms using digital signature techniques. Tech. rep. (Jan 2019)

 A -> B: {A, gx}                            msg1
 B -> A: {B, gy, sign({A; gx; gy}, privB)}  msg2
 A -> B: {sign({B; gx; gy}, privA)}         msg3

*)

(*** Definition of messages ***)
// Annotation is needed for comparse to generate serialization methods
[@@ with_bytes bytes]
type message1 = {
  alice:principal;
  gx:bytes;
}

%splice [ps_message1] (gen_parser (`message1))
%splice [ps_message1_is_well_formed] (gen_is_well_formed_lemma (`message1))

[@@ with_bytes bytes]
type message2 = {
  bob:principal;
  gy:bytes;
  sg:bytes;
}

%splice [ps_message2] (gen_parser (`message2))
%splice [ps_message2_is_well_formed] (gen_is_well_formed_lemma (`message2))

[@@ with_bytes bytes]
type message3 = {
  sg:bytes;
}

%splice [ps_message3] (gen_parser (`message3))
%splice [ps_message3_is_well_formed] (gen_is_well_formed_lemma (`message3))


[@@ with_bytes bytes]
type message =
  | Msg1: msg:message1 -> message
  | Msg2: msg:message2 -> message
  | Msg3: msg:message3 -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message

// Definition of signature terms
[@@ with_bytes bytes]
type sig_message2 = {
  alice:principal;
  gx:bytes;
  gy:bytes;
}

%splice [ps_sig_message2] (gen_parser (`sig_message2))
%splice [ps_sig_message2_is_well_formed] (gen_is_well_formed_lemma (`sig_message2))

[@@ with_bytes bytes]
type sig_message3 = {
  bob:principal;
  gx:bytes;
  gy:bytes;
}

%splice [ps_sig_message3] (gen_parser (`sig_message3))
%splice [ps_sig_message3_is_well_formed] (gen_is_well_formed_lemma (`sig_message3))

[@@ with_bytes bytes]
type sig_message =
  | SigMsg2: msg:sig_message2 -> sig_message
  | SigMsg3: msg:sig_message3 -> sig_message

%splice [ps_sig_message] (gen_parser (`sig_message))
%splice [ps_sig_message_is_well_formed] (gen_is_well_formed_lemma (`sig_message))

instance parseable_serializeable_sig_message: parseable_serializeable bytes sig_message = mk_parseable_serializeable ps_sig_message


(*** Message Processing ***)

// Alice generates message 1
val compute_message1: principal -> bytes -> bytes
let compute_message1 alice x =
  let gx = dh_pk x in
  let msg = Msg1 {alice; gx} in
  serialize message msg

// Bob parses message 1
val decode_message1: bytes -> option message1
let decode_message1 msg1_bytes =
  let? msg1 = parse message msg1_bytes in
  // These lines are the...
  guard (Msg1? msg1);?
  Some (Msg1?.msg msg1)
  // ...short version of the following match:
  (*    
  match msg1 with
  | Msg1 msg -> Some msg
  | _ -> None
  *)

// Bob generates message 2
val compute_message2: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes
let compute_message2 alice bob gx gy sk_b n_sig =
  let sig_msg = SigMsg2 {alice; gx; gy} in
  let sg = sign sk_b n_sig (serialize sig_message sig_msg) in
  let msg = Msg2 {bob; gy; sg} in
  serialize message msg

// Alice parses message 2
type verify_msg2_result = {sg:bytes; gy:bytes; gx:bytes; k:bytes}
val decode_and_verify_message2: bytes -> principal -> bytes -> bytes -> option verify_msg2_result
let decode_and_verify_message2 msg2_bytes alice x pk_b =
  let? msg2_parsed = parse message msg2_bytes in
  guard (Msg2? msg2_parsed);?
  let msg2 = Msg2?.msg msg2_parsed in
  // Verify the signature contained in the message 2
  // with the gy value from the message and the gx
  // value from Alice's state.
  let gx = dh_pk x in
  let gy = msg2.gy in
  let sig_msg = SigMsg2 {alice; gx; gy} in
  // These lines are the...
  guard(verify pk_b (serialize sig_message sig_msg) msg2.sg);?
  let k = dh x gy in
  Some {sg=msg2.sg; gy; gx; k}
  // ...short version of the following if-else block:
  (*  
  if verify pk_b (serialize sig_message sig_msg) msg2.sg then Some {msg2; gx; k}
  else None
  *)

// Alice generates message3
val compute_message3: principal -> principal -> bytes -> bytes -> bytes -> bytes -> bytes
let compute_message3 alice bob gx gy sk_a n_sig =
  let sig_msg = SigMsg3 {bob; gx; gy} in
  let sg = sign sk_a n_sig (serialize sig_message sig_msg) in
  let msg = Msg3 {sg} in
  serialize message msg

// Bob parses message3
type verify_msg3_result = {sg:bytes; k:bytes}
val decode_and_verify_message3: bytes -> principal -> bytes -> bytes -> bytes -> bytes -> option verify_msg3_result
let decode_and_verify_message3 msg3_bytes bob gx gy y pk_a =
  let? msg3_parsed = parse message msg3_bytes in
  guard (Msg3? msg3_parsed);?
  let msg3:message3 = Msg3?.msg msg3_parsed in
  // Verify the signature contained in message 3
  // with the gx and gy values from Bob's state.
  let sig_msg = SigMsg3 {bob; gx; gy} in
  guard(verify pk_a (serialize sig_message sig_msg) msg3.sg);?
  let k = dh y gx in
  Some {sg=msg3.sg; k}
