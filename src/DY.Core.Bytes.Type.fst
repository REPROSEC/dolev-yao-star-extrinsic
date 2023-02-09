module DY.Core.Bytes.Type

open DY.Core.Label.Type

type bytes =
  | Literal: FStar.Seq.seq FStar.UInt8.t -> bytes
  | Rand: label:label -> len:nat{len <> 0} -> time:nat -> bytes //TODO

  | Concat: left:bytes -> right:bytes -> bytes

  // Authenticated (private key) Encryption with Additional Data
  | Aead: key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes -> bytes

  // Public key encryption
  | Pk: sk:bytes -> bytes
  | PkEnc: pk:bytes -> nonce:bytes -> msg:bytes -> bytes

  // Signature
  | Vk: sk:bytes -> bytes
  | Sign: sk:bytes -> nonce:bytes -> msg:bytes -> bytes

  // ...
