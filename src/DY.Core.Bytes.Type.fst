module DY.Core.Bytes.Type

open DY.Core.Label.Type

type usage_ (bytes:Type0) =
  | SigKey: label:string -> usage_ bytes
  | PkdecKey: label:string -> usage_ bytes
  | AeadKey: label:string -> usage_ bytes
  | Unknown: usage_ bytes // baked-in None

type bytes =
  | Literal: FStar.Seq.seq FStar.UInt8.t -> bytes
  | Rand: usage:usage_ bytes -> label:label -> len:nat{len <> 0} -> time:nat -> bytes

  | Concat: left:bytes -> right:bytes -> bytes

  // Authenticated (private key) Encryption with Additional Data
  | Aead: key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes -> bytes

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
