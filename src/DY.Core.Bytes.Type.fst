module DY.Core.Bytes.Type

open DY.Core.Label.Type

/// This module defines the types associated with bytes.
/// It is separated from functions and predicates on bytes
/// in order to avoid dependency cycles.

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
/// Second, the various usages additionally contain a usage string,
/// which is used to further distinguish keys used with a given cryptographic primitive:
/// for example to distinguish the long-term key from the ephemeral ones,
/// or to distinguish keys from two sub-protocols running in parallel.
/// At the end, this usage string may play a role in the security proof
/// via the protocol invariants.

type usage_ (bytes:Type0) =
  | SigKey: tag:string -> usage_ bytes
  | SigNonce: usage_ bytes
  | PkdecKey: tag:string -> usage_ bytes
  | PkNonce: usage_ bytes
  | AeadKey: tag:string -> usage_ bytes
  | NoUsage: usage_ bytes // baked-in None

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
  | Rand: usage:usage_ bytes -> label:label -> len:nat{len <> 0} -> time:nat -> bytes

  // Concatenation
  | Concat: left:bytes -> right:bytes -> bytes

  // Authenticated (private key) Encryption with Additional Data
  | AeadEnc: key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes -> bytes

  // Public key encryption
  | Pk: sk:bytes -> bytes
  | PkEnc: pk:bytes -> nonce:bytes -> msg:bytes -> bytes

  // Signature
  | Vk: sk:bytes -> bytes
  | Sign: sk:bytes -> nonce:bytes -> msg:bytes -> bytes

  // Hash
  | Hash: msg:bytes -> bytes

  // ...

type usage = usage_ bytes
