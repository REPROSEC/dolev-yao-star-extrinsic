module DY.Core.Bytes.Type

/// This module defines the types associated with bytes.
/// It is separated from functions and predicates on bytes
/// in order to avoid dependency cycles.

/// The bytes term.
/// It is similar to the one you would find in other symbolic analysis tools.
/// One notable difference is that this one only contains "constructors" (e.g. encryption)
/// and omit "destructors" (e.g. decryption).
/// This is because while other symbolic analysis tools
/// often reason on equality modulo some rewriting rules
/// (such as `dec(k, enc(k, msg)) == msg`).
/// Reasoning on equality "modulo something" in F* is cumbersome.
/// Instead, the destructors (e.g. decryption) will inspect the bytes
/// and return the data you would obtain via the reduction rule
/// (e.g. the plaintext if the bytes is an encryption with the correct key).
/// This allows us to reason with F*'s logical equality (`==`).

type bytes =
  // Public values (strings, numbers, ...)
  | Literal: FStar.Seq.seq FStar.UInt8.t -> bytes
  // Randomly generated numbers. `time` is used to ensure two random numbers are distinct.
  | Rand: len:nat{len <> 0} -> time:nat -> bytes

  // Concatenation
  | Concat: left:bytes -> right:bytes -> bytes

  // Authenticated (private key) Encryption with Additional Data
  | AeadEnc: key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes -> bytes

  // Public key encryption
  | Pk: sk:bytes -> bytes
  | PkeEnc: pk:bytes -> nonce:bytes -> msg:bytes -> bytes

  // Signature
  | Vk: sk:bytes -> bytes
  | Sign: sk:bytes -> nonce:bytes -> msg:bytes -> bytes

  // Hash
  | Hash: msg:bytes -> bytes

  // Diffie-Hellman
  | DhPub: sk:bytes -> bytes
  | Dh: sk:bytes -> pk:bytes -> bytes

  // Key Derivation Function
  | KdfExtract: salt:bytes -> ikm:bytes -> bytes
  | KdfExpand: prk:bytes -> info:bytes -> len:nat{len <> 0} -> bytes

  // Key Encapsulation Mechanism
  | KemPub: sk:bytes -> bytes
  | KemEncap: pk:bytes -> ss:bytes -> bytes
  | KemSecretShared: ss:bytes -> bytes

  | Mac: key:bytes -> msg:bytes -> bytes

  // ...

/// Usages depict how a given bytestring will be cryptographically used.
///
/// First, it will say whether a bytestring is e.g. a signature key or a symetric encryption key.
/// Usual symbolic analysis tools, such as ProVerif or Tamarin,
/// will not object if you use a bytestring as key material for two different cryptographic primitives.
/// This is something that must be avoided in secure cryptographic protocols:
/// indeed, standard security assumptions do not apply when we use the same key for different cryptographic primitives.
/// In DY*, usages ensure that a cryptographic protocol
/// do not use the same bytestring as the key for different cryptographic primitives.
/// To this bytestring will correspond a usage (e.g. "SigKey"),
/// which will ensure it can only be used as the key of one specific cryptographic primitive (e.g. signature function).
///
/// Second, the various usages additionally contain a usage string "tag",
/// which is used to further distinguish keys used with a given cryptographic primitive:
/// for example to distinguish the long-term key from the ephemeral ones,
/// or to distinguish keys from two sub-protocols running in parallel.
/// At the end, this usage string may play a role in the security proof
/// via the protocol invariants.
///
/// Because a string may not be enough to express the complex reasons two keys are distinct,
/// usages also contain a `bytes` called "data".
/// This is useful to do security proofs of protocols with complex key schedules,
/// allowing the usage's `data` field and the label of the keys to evolve
/// when calling kdf_extract and kdf_expand.

type usage =
  | NoUsage: usage // baked-in None
  | SigKey: tag:string -> data:bytes -> usage
  | SigNonce: usage
  | PkeKey: tag:string -> data:bytes -> usage
  | PkeNonce: usage
  | AeadKey: tag:string -> data:bytes -> usage
  | DhKey: tag:string -> data:bytes -> usage
  | KdfExpandKey: tag:string -> data:bytes -> usage
  | KemKey: usg:usage -> usage
  | KemNonce: usg:usage -> usage
  | MacKey: tag:string -> data:bytes -> usage

open DY.Core.Internal.Ord

val encode_bytes: bytes -> list int
let rec encode_bytes b =
  match b with
  | Literal l -> 0::(encode_list [encode l])
  | Rand len time -> 1::(encode_list [encode (len <: nat); encode time])
  | Concat left right -> 2::(encode_list [encode_bytes left; encode_bytes right])
  | AeadEnc key nonce msg ad -> 3::(encode_list [encode_bytes key; encode_bytes nonce; encode_bytes msg; encode_bytes ad])
  | Pk sk -> 4::(encode_list [encode_bytes sk])
  | PkeEnc pk nonce msg -> 5::(encode_list [encode_bytes pk; encode_bytes nonce; encode_bytes msg])
  | Vk sk -> 6::(encode_list [encode_bytes sk])
  | Sign sk nonce msg -> 7::(encode_list [encode_bytes sk; encode_bytes nonce; encode_bytes msg])
  | Hash msg -> 8::(encode_list [encode_bytes msg])
  | DhPub sk -> 9::(encode_list [encode_bytes sk])
  | Dh sk pk -> 10::(encode_list [encode_bytes sk; encode_bytes pk])
  | KdfExtract salt ikm -> 11::(encode_list [encode_bytes salt; encode_bytes ikm])
  | KdfExpand prk info len -> 12::(encode_list [encode_bytes prk; encode_bytes info; encode (len <: nat)])
  | KemPub sk -> 13::(encode_list [encode_bytes sk])
  | KemEncap pk ss -> 14::(encode_list [encode_bytes pk; encode_bytes ss])
  | KemSecretShared ss -> 15::(encode_list [encode_bytes ss])
  | Mac key msg -> 16::(encode_list [encode_bytes key; encode_bytes msg])

#push-options "--z3rlimit 25 --fuel 3 --ifuel 3"
val encode_bytes_inj: b1:bytes -> b2:bytes -> Lemma (requires encode_bytes b1 == encode_bytes b2) (ensures b1 == b2)
let rec encode_bytes_inj b1 b2 =
  encode_inj_forall (list (list int)) ();
  match b1, b2 with
  | Literal x1, Literal x2 ->
    encode_list_inj [encode x1] [encode x2];
    encode_inj x1 x2
  | Rand x1 x2, Rand y1 y2 ->
    encode_list_inj [encode (x1 <: nat); encode x2] [encode (y1 <: nat); encode y2];
    encode_inj x1 y1;
    encode_inj x2 y2
  | Pk x1, Pk y1
  | Vk x1, Vk y1
  | Hash x1, Hash y1
  | DhPub x1, DhPub y1
  | KemPub x1, KemPub y1
  | KemSecretShared x1, KemSecretShared y1 ->
    encode_list_inj [encode_bytes x1] [encode_bytes y1];
    encode_bytes_inj x1 y1
  | Concat x1 x2, Concat y1 y2
  | Dh x1 x2, Dh y1 y2
  | KdfExtract x1 x2, KdfExtract y1 y2
  | KdfExpand x1 x2 _, KdfExpand y1 y2 _
  | KemEncap x1 x2, KemEncap y1 y2
  | Mac x1 x2, Mac y1 y2 ->
    encode_bytes_inj x1 y1;
    encode_bytes_inj x2 y2
  | PkeEnc x1 x2 x3, PkeEnc y1 y2 y3
  | Sign x1 x2 x3, Sign y1 y2 y3 ->
    encode_bytes_inj x1 y1;
    encode_bytes_inj x2 y2;
    encode_bytes_inj x3 y3
  | AeadEnc x1 x2 x3 x4, AeadEnc y1 y2 y3 y4 ->
    encode_bytes_inj x1 y1;
    encode_bytes_inj x2 y2;
    encode_bytes_inj x3 y3;
    encode_bytes_inj x4 y4
  | _, _ -> assert(False)
#pop-options

instance integer_encodable_bytes: integer_encodable bytes = {
  encode = encode_bytes;
  encode_inj = encode_bytes_inj;
}
