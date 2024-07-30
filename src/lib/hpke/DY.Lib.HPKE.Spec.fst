module DY.Lib.HPKE.Spec

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

#set-options "--fuel 0 --ifuel 1"

/// This module defines the specification of HPKE.
/// More precisely, this specification corresponds to the single-shot API in base mode
/// (c.f. section 6.1 of RFC 9180 [1]).
///
/// This specification has the following limitations:
/// - the message formatting is not compliant with RFC 9180 (e.g. the one in LabeledExpand)
/// - some KDF.Extract were omitted, for example:
///   - `info` is extracted before going to LabeledExpand's info
///   - `shared_secret` is extracted with the empty PSK
///      before going to LabeledExpand's prk
///   (c.f. section 5.1 of RFC 9180 [2])
/// Having a more compliant specification is left as future work.
///
/// [1] https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-and-decryption-2
/// [2] https://www.rfc-editor.org/rfc/rfc9180.html#name-creating-the-encryption-con

/// Definition of the internal function LabeledExpand

[@@ with_bytes bytes]
type hpke_labeled_expand_info = {
  len: nat_lbytes 2;
  [@@@ with_parser #bytes ps_string]
  label: string;
  info: bytes;
}

%splice [ps_hpke_labeled_expand_info] (gen_parser (`hpke_labeled_expand_info))
%splice [ps_hpke_labeled_expand_info_is_well_formed] (gen_is_well_formed_lemma (`hpke_labeled_expand_info))

instance parseable_serializeable_bytes_hpke_labeled_expand_info: parseable_serializeable bytes hpke_labeled_expand_info =
  mk_parseable_serializeable ps_hpke_labeled_expand_info

val hpke_labeled_expand: bytes -> string -> bytes -> len:nat_lbytes 2{len <> 0} -> bytes
let hpke_labeled_expand prk label info len =
  kdf_expand prk (serialize _ { len; label; info }) len

/// The HPKE functions

val hpke_pk: bytes -> bytes
let hpke_pk sk =
  kem_pk sk

val hpke_enc: bytes -> bytes -> bytes -> bytes -> bytes -> (bytes & bytes)
let hpke_enc pkR entropy plaintext info ad =
  let (enc, shared_secret) = kem_encap pkR entropy in
  let aead_key = hpke_labeled_expand shared_secret "key" info 32 in
  let aead_nonce = hpke_labeled_expand shared_secret "nonce" info 32 in
  let cipher = aead_enc aead_key aead_nonce plaintext ad in
  (enc, cipher)

val hpke_dec: bytes -> (bytes & bytes) -> bytes -> bytes -> option bytes
let hpke_dec skR (enc, ciphertext) info ad =
  match kem_decap skR enc with
  | None -> None
  | Some shared_secret ->
    let aead_key = hpke_labeled_expand shared_secret "key" info 32 in
    let aead_nonce = hpke_labeled_expand shared_secret "nonce" info 32 in
    aead_dec aead_key aead_nonce ciphertext ad
