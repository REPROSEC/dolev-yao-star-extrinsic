module DY.Lib.HPKE.Lemmas

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers
open DY.Lib.HPKE.Spec
open DY.Lib.Crypto.AEAD.Split
open DY.Lib.Crypto.KdfExpand.Split

#set-options "--fuel 0 --ifuel 1"

/// This module proves security theorems about HPKE, in a modular and reusable way.
/// The security theorems are similar to the public key encryption ones
/// (e.g. DY.Core.Bytes.bytes_invariant_pk_dec).
///
/// The modularity is achieved using the split invariant mechanism for AEAD and KdfExpand,
/// allowing for horizontal protocol composition.
/// The proofs are parametrized by a global HPKE predicate `hpke_crypto_predicate`
/// (similar to DY.Core.pke_crypto_predicate)
/// which is then compiled to a (local) AEAD predicate (see `hpke_aead_pred`),
/// allowing for vertical protocol composition.
///
/// The proof sketch is the following:
/// - the shared secret is a KdfExpandKey with usage tag "DY.Lib.HPKE"
/// - the HPKE usage tag and usage data is serialized into the KdfExpandKey usage data
///   (using the type `internal_hpke_usage`)
/// - when the shared secret goes into kdf_expand with `info`,
///   we obtain an AeadKey with usage tag "DY.Lib.HPKE"
///   and usage data containing `info` and the HPKE key usage
///   (using the type `hpke_aead_usage_data`, see `hpke_kdf_expand_usage`)
/// - when encrypting or decrypting with AEAD,
///   `plaintext` and `ad` are authenticated by AEAD,
///   the HPKE usage and `info` are authenticated in the usage data of the AEAD key.

/// Symbolic reduction rule (sanity check)

val hpke_dec_enc:
  skR:bytes -> entropy:bytes -> plaintext:bytes -> info:bytes -> ad:bytes ->
  Lemma
  (hpke_dec skR (hpke_enc (hpke_pk skR) entropy plaintext info ad) info ad == Some plaintext)
let hpke_dec_enc skR entropy plaintext info ad =
  FStar.Classical.forall_intro_2 kem_decap_encap;
  FStar.Classical.forall_intro_4 aead_dec_enc

/// Helper functions to create hpke usages (secret key and entropy)

[@@ with_bytes bytes]
type internal_hpke_usage = {
  [@@@ with_parser #bytes ps_string]
  usage_tag: string;
  usage_data: bytes;
}

%splice [ps_internal_hpke_usage] (gen_parser (`internal_hpke_usage))

instance parseable_serializeable_bytes_internal_hpke_usage: parseable_serializeable bytes internal_hpke_usage =
  mk_parseable_serializeable ps_internal_hpke_usage

val mk_hpke_sk_usage: string & bytes -> usage
let mk_hpke_sk_usage (usage_tag, usage_data) =
  KemKey (KdfExpandKey "DY.Lib.HPKE" (serialize _ {usage_tag; usage_data}))

val mk_hpke_entropy_usage: string & bytes -> usage
let mk_hpke_entropy_usage (usage_tag, usage_data) =
  KemNonce (KdfExpandKey "DY.Lib.HPKE" (serialize _ {usage_tag; usage_data}))

/// Obtain the label of the corresponding HPKE private key of a HPKE public key.

val get_hpke_sk_label: {|crypto_usages|} -> trace -> bytes -> label
let get_hpke_sk_label #cusages tr pk =
  get_kem_sk_label tr pk

/// Obtain the usage of the corresponding HPKE private key of a HPKE public key.

val has_hpke_sk_usage: {|crypto_usages|} -> trace -> bytes -> usage -> prop
let has_hpke_sk_usage #cusages tr pk usg =
  pk `has_kem_sk_usage tr` usg

/// Type for the HPKE predicate

noeq
type hpke_crypto_predicate {|crypto_usages|} = {
  pred: tr:trace -> usage:(string & bytes) -> pkR:bytes{pkR `has_hpke_sk_usage tr` (mk_hpke_sk_usage usage)} -> msg:bytes -> info:bytes -> ad:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    usage:(string & bytes) -> pkR:bytes -> msg:bytes -> info:bytes -> ad:bytes ->
    Lemma
    (requires
      pkR `has_hpke_sk_usage tr1` (mk_hpke_sk_usage usage) /\
      pred tr1 usage pkR msg info ad /\
      bytes_well_formed tr1 pkR /\
      bytes_well_formed tr1 msg /\
      bytes_well_formed tr1 info /\
      bytes_well_formed tr1 ad /\
      tr1 <$ tr2
    )
    (ensures pred tr2 usage pkR msg info ad)
  ;
}

/// Typeclass for hpke_crypto_predicate.
/// The type `hpke_crypto_predicate` is used to represent the global HPKE predicate,
/// but could also be used to represent local HPKE predicates,
/// as it is done e.g. with sign_crypto_predicate.
/// Hence, we cannot use the typeclass mechanism directly on `hpke_crypto_predicate`,
/// as the typeclass resolution algorithm might resolve to local predicates.
/// Hence, similarly to how we access to the global `sign_crypto_predicate` through the typeclass `crypto_invariants`,
/// we define `hpke_crypto_invariants` that will contain the global HPKE predicate.

class hpke_crypto_invariants {|crypto_usages|} = {
  hpke_pred: hpke_crypto_predicate;
}

/// The cryptographic invariants for HPKE.

[@@ with_bytes bytes]
type hpke_aead_usage_data = {
  hpke_usg: internal_hpke_usage;
  info: bytes;
}

%splice [ps_hpke_aead_usage_data] (gen_parser (`hpke_aead_usage_data))

instance parseable_serializeable_bytes_hpke_aead_usage_data: parseable_serializeable bytes hpke_aead_usage_data =
  mk_parseable_serializeable ps_hpke_aead_usage_data

let hpke_kdf_expand_usage: kdf_expand_crypto_usage = {
  get_usage = (fun prk_usage info ->
    let KdfExpandKey _ data = prk_usage in
    match parse hpke_labeled_expand_info info, parse internal_hpke_usage data with
    | Some { len; label = "key"; info }, Some hpke_usg ->
      AeadKey "DY.Lib.HPKE" (serialize _ { hpke_usg; info; })
    | Some { len; label = "base_nonce"; info }, Some hpke_usg ->
      NoUsage // AEAD nonce
    | _ ->
      NoUsage
  );
  get_label = (fun prk_usage prk_label info ->
    match parse hpke_labeled_expand_info info with
    | Some { len; label = "key"; info } ->
      prk_label
    | Some { len; label = "base_nonce"; info } ->
      public
    | _ ->
      prk_label
  );
  get_label_lemma = (fun tr prk_usage prk_label info -> ());
}

val hpke_aead_pred: {|crypto_usages|} -> {|hpke_crypto_invariants|} -> aead_crypto_predicate
let hpke_aead_pred #cusgs #hpke = {
  pred = (fun tr key_usage key nonce msg ad ->
    let AeadKey usg data = key_usage in
    assert(key `has_usage tr` key_usage);
    match parse hpke_aead_usage_data data with
    | Some { hpke_usg; info; } ->
      bytes_well_formed tr info /\ (
        get_label tr msg `can_flow tr` public \/
        (key `has_hpke_sk_usage tr` (mk_hpke_sk_usage (hpke_usg.usage_tag, hpke_usg.usage_data)) /\
        hpke_pred.pred tr (hpke_usg.usage_tag, hpke_usg.usage_data) key msg info ad)
      )
    | _ ->
      False
  );
  pred_later = (fun tr1 tr2 key_usage key nonce msg ad ->
    let AeadKey usg data = key_usage in
    match parse hpke_aead_usage_data data with
    | Some { hpke_usg; info; } ->
      introduce ~(get_label tr1 msg `can_flow tr1` public) ==>
        hpke_pred.pred tr2 (hpke_usg.usage_tag, hpke_usg.usage_data) key msg info ad
      with _. (
        hpke_pred.pred_later tr1 tr2 (hpke_usg.usage_tag, hpke_usg.usage_data) key msg info ad
      )
    | _ -> ()
  );
}

/// Integration of the invariants within the split predicate methodology

let hpke_kdf_expand_tag_and_usage = ("DY.Lib.HPKE", hpke_kdf_expand_usage)

val has_hpke_kdf_expand_usage: {|crypto_usages|} -> prop
let has_hpke_kdf_expand_usage #cusgs =
  has_kdf_expand_usage hpke_kdf_expand_tag_and_usage

let hpke_aead_tag_and_pred {|crypto_usages|} {|hpke_crypto_invariants|} = ("DY.Lib.HPKE", hpke_aead_pred)

val has_hpke_aead_pred: {|crypto_invariants|} -> {|hpke_crypto_invariants|} -> prop
let has_hpke_aead_pred #cinvs #hpke =
  has_aead_predicate hpke_aead_tag_and_pred

val has_hpke_invariants: {|crypto_invariants|} -> {|hpke_crypto_invariants|} -> prop
let has_hpke_invariants #cinvs #hpke =
  has_hpke_kdf_expand_usage /\
  has_hpke_aead_pred

/// Lemmas for `hpke_pk`

val bytes_invariant_hpke_pk:
  {|crypto_invariants|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant tr sk)
  (ensures bytes_invariant tr (hpke_pk sk))
  [SMTPat (bytes_invariant tr (hpke_pk sk))]
let bytes_invariant_hpke_pk #ci tr sk = ()

val get_label_hpke_pk:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures get_label tr (hpke_pk sk) == public)
  [SMTPat (get_label tr (hpke_pk sk))]
let get_label_hpke_pk #cu tr sk = ()

val has_hpke_sk_usage_hpke_pk:
  {|crypto_usages|} ->
  tr:trace -> sk:bytes -> usg:usage ->
  Lemma
  (ensures (hpke_pk sk) `has_hpke_sk_usage tr` usg == sk `has_usage tr` usg)
  [SMTPat ((hpke_pk sk) `has_hpke_sk_usage tr` usg)]
let has_hpke_sk_usage_hpke_pk #cu tr sk usg = ()

val get_hpke_sk_label_hpke_pk:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures get_hpke_sk_label tr (hpke_pk sk) == get_label tr sk)
  [SMTPat (get_hpke_sk_label tr (hpke_pk sk))]
let get_hpke_sk_label_hpke_pk #cu tr sk = ()

/// Lemma for `hpke_enc`.
/// It is a bit more complex than `DY.Core.Bytes.bytes_invariant_pk_enc`,
/// the additional complexity is explained in the comments.

#push-options "--ifuel 2 --z3rlimit 50"
val bytes_invariant_hpke_enc:
  {|crypto_invariants|} -> {|hpke_crypto_invariants|} ->
  tr:trace ->
  pkR:bytes -> entropy:bytes -> msg:bytes -> info:bytes -> ad:bytes ->
  usg:(string & bytes) ->
  Lemma
  (requires
    bytes_invariant tr pkR /\
    bytes_invariant tr entropy /\
    bytes_invariant tr msg /\
    bytes_invariant tr info /\
    is_publishable tr ad /\
    // the message must flow to the shared secret (derived from the entropy), a requirement of AEAD
    (get_label tr msg) `can_flow tr` (get_label tr entropy) /\
    // shared secret (derived from the entropy) must flow to the secret key, a requirement of KEM
    (get_label tr entropy) `can_flow tr` (get_hpke_sk_label tr pkR) /\
    // the entropy and public key must agree on the usage,
    // or the entropy (hence shared secret) must be publishable:
    // without this precondition, there could be cross-protocol attacks,
    // e.g. if a public key of ProtocolA is injected in ProtocolB by the attacker,
    // then the sender sends a secret to this public key (safe by ProtocolB invariants)
    // but the receiver expect messages encrypted to this public key to be public (safe by ProtocolA invariants)
    entropy `has_usage tr` mk_hpke_entropy_usage usg /\
    (
      (
        pkR `has_hpke_sk_usage tr` mk_hpke_sk_usage usg /\
        hpke_pred.pred tr usg pkR msg info ad
      ) \/ (
        get_label tr entropy `can_flow tr` public
      )
    ) /\
    // the global protocol invariants must contain the HPKE invariants
    has_hpke_invariants
  )
  (ensures (
    let (enc, ciphertext) = hpke_enc pkR entropy msg info ad in
    is_publishable tr enc /\
    is_publishable tr ciphertext
  ))
  [SMTPat (hpke_enc pkR entropy msg info ad);
   SMTPat (bytes_invariant tr msg);
   SMTPat (has_hpke_invariants);
   SMTPat (entropy `has_usage tr` mk_hpke_entropy_usage usg)
  ]
let bytes_invariant_hpke_enc #cinvs #hpke tr pkR entropy msg info ad (usage_tag, usage_data) =
  let (enc, shared_secret) = kem_encap pkR entropy in
  bytes_invariant_kem_encap tr pkR entropy (KdfExpandKey "DY.Lib.HPKE" (serialize _ {usage_tag; usage_data}));
  let aead_key = kdf_expand shared_secret (serialize _ { len = 32; label = "key"; info }) 32 in
  let aead_nonce = kdf_expand shared_secret (serialize _ { len = 32; label = "base_nonce"; info }) 32 in
  assert(aead_key `has_usage tr` AeadKey "DY.Lib.HPKE" (serialize _ {hpke_usg = {usage_tag; usage_data}; info}));

  let ciphertext = aead_enc aead_key aead_nonce msg ad in
  assert((enc, ciphertext) == hpke_enc pkR entropy msg info ad);

  //assert(hpke_pred.pred tr (usage_tag, usage_data) pkR msg info ad);
  let key_usage = (AeadKey "DY.Lib.HPKE" (serialize _ {hpke_usg = {usage_tag; usage_data}; info})) in
  assert(
    get_label tr msg `can_flow tr` public \/
    (
      pkR `has_hpke_sk_usage tr` (mk_hpke_sk_usage (usage_tag, usage_data)) ///\
      //hpke_pred.pred tr (usage_tag, usage_data) pkR msg info ad
    )
  );
  assert(
    let AeadKey usg data = key_usage in
    assert(aead_key `has_usage tr` key_usage);
    match parse hpke_aead_usage_data data with
    | Some { hpke_usg; info; } ->
      bytes_well_formed tr info /\ (
        get_label tr msg `can_flow tr` public \/
        (pkR `has_hpke_sk_usage tr` (mk_hpke_sk_usage (hpke_usg.usage_tag, hpke_usg.usage_data)) /\
        hpke_pred.pred tr (hpke_usg.usage_tag, hpke_usg.usage_data) pkR msg info ad)
      )
    | _ ->
      False
  );
  assume(
    pkR `has_hpke_sk_usage tr` mk_hpke_sk_usage (usage_tag, usage_data) /\
    hpke_pred.pred tr (usage_tag, usage_data) pkR msg info ad ==> aead_pred.pred tr (AeadKey "DY.Lib.HPKE" (serialize _ {hpke_usg = {usage_tag; usage_data}; info})) aead_key aead_nonce msg ad);
  serialize_wf_lemma _ (bytes_invariant tr) { len = 32; label = "key"; info };
  serialize_wf_lemma _ (bytes_invariant tr) { len = 32; label = "base_nonce"; info };
  ()
#pop-options

/// HPKE decryption theorem.
/// It is similar to `DY.Core.Bytes.bytes_invariant_pk_dec`.

#push-options "--ifuel 0"
val bytes_invariant_hpke_dec:
  {|crypto_invariants|} -> {|hpke_crypto_invariants|} ->
  tr:trace ->
  skR:bytes -> enc:bytes -> ciphertext:bytes -> info:bytes -> ad:bytes ->
  usg:(string & bytes) ->
  Lemma
  (requires
    bytes_invariant tr skR /\
    skR `has_usage tr` mk_hpke_sk_usage usg /\
    bytes_invariant tr enc /\
    bytes_invariant tr ciphertext /\
    bytes_invariant tr info /\
    bytes_invariant tr ad /\
    has_hpke_invariants
  )
  (ensures (
    match hpke_dec skR (enc, ciphertext) info ad with
    | None -> True
    | Some plaintext ->
      is_knowable_by (get_label tr skR) tr plaintext /\
      (
        (
          hpke_pred.pred tr usg (hpke_pk skR) plaintext info ad
        ) \/ (
          is_publishable tr plaintext
        )
      )
  ))
  [SMTPat (hpke_dec skR (enc, ciphertext) info ad);
   SMTPat (bytes_invariant tr ciphertext);
   SMTPat (has_hpke_invariants);
   SMTPat (skR `has_usage tr` mk_hpke_sk_usage usg);
  ]
let bytes_invariant_hpke_dec #cinvs #hpke tr skR enc ciphertext info ad (usage_tag, usage_data) =
  let key_info = { len = 32; label = "key"; info } in
  let key_info_bytes = serialize _ key_info in
  let nonce_info = { len = 32; label = "base_nonce"; info } in
  let nonce_info_bytes = serialize _ nonce_info in
  serialize_wf_lemma _ (bytes_invariant tr) key_info;
  serialize_wf_lemma _ (bytes_invariant tr) nonce_info;

  match kem_decap skR enc with
  | None -> ()
  | Some shared_secret -> (
    // The `assert`s below are not needed for the proof to work.
    // They are however useful to debug the proof when tweaking invariants
    // or tweaking the specification.
    // This is why we leave these here.
    assert(bytes_invariant tr shared_secret);
    assert(shared_secret `has_usage tr` KdfExpandKey "DY.Lib.HPKE" (serialize _ {usage_tag; usage_data}));
    let aead_key = kdf_expand shared_secret key_info_bytes 32 in
    assert(aead_key `has_usage tr` AeadKey "DY.Lib.HPKE" (serialize _ {hpke_usg = {usage_tag; usage_data}; info}));
    assert(get_label tr aead_key `equivalent tr` get_label tr shared_secret);
    let aead_nonce = kdf_expand shared_secret nonce_info_bytes 32 in
    assert(aead_nonce `has_usage tr` NoUsage);
    assert(get_label tr aead_nonce `equivalent tr` public);
    match aead_dec aead_key aead_nonce ciphertext ad with
    | None -> ()
    | Some plaintext -> (
      assume((aead_pred.pred tr (AeadKey "DY.Lib.HPKE" (serialize _ {hpke_usg = {usage_tag; usage_data}; info})) aead_key aead_nonce plaintext ad ==> (hpke_pred.pred tr (usage_tag, usage_data) (hpke_pk skR) plaintext info ad \/ is_publishable tr plaintext)))
    )
  )
#pop-options
