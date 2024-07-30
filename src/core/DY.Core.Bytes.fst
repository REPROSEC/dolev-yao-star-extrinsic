module DY.Core.Bytes

open DY.Core.Bytes.Type
open DY.Core.Trace.Type
open DY.Core.Label.Type
open DY.Core.Label
open DY.Core.Label.Derived

#set-options "--fuel 1 --ifuel 1"

/// This module contains functions and predicates operating on bytes.
///
/// To conduct security proofs, a crucial predicate is the `bytes_invariant`,
/// an invariant on all the bytes being used in a protocol execution.
/// This is invariant is preserved by honest participants
/// (something which we need to prove on protocols analyzed with DY*),
/// and is also preserved by the attacker
/// (which preserve a stronger invariant, publishability, more on that below).
///
/// Because each cryptographic protocol need a custom bytes invariant to be proved secure,
/// the bytes invariant can be customised with `crypto_invariants` specific to a protocol.
/// For example, they can be used to ensure that honest participants
/// only sign bytestrings that satisfy some predicate (namely, the signature predicate `sign_pred`).
/// In return, when a signature verifies,
/// we can deduce that the signed bytestring verifies the signature predicate
/// (or that the signature key is known to the attacker).
///
/// Security proofs also rely on the essential notion of labels,
/// an approximation of the set of principals that know some bytestring
/// (see DY.Core.Label for more detailed explanations),
/// which are used to define the cryptographic invariants.
/// Labels are then used to define the "publishability" predicate (`is_publishable`),
/// which states that a given bytestring satisfy the bytes invariant,
/// and has a label equivalent to "public", i.e. its content is not secret
/// (either because it's public data, or because the attacker corrupted some principal).
/// The publishability predicate is then used to state the attacker knowledge theorem of DY*:
/// if the attacker knows a bytestring `b`, then `b` is publishable.
/// (This theorem is proved in DY.Core.Attacker.Knowledge.attacker_only_knows_publishable_values.)
/// (In turn, if we know `b` is a secret key,
/// this fact could be used to further deduce that the attacker must have compromised some principal.)
///
/// The definition of every cryptographic primitive will have the following structure:
/// - definition of the constructors (e.g. encryption) and destructors (e.g. decryption)
/// - reduction theorems
///   (e.g. the decryption of an encryption gives back the plaintext)
/// - lemmas for the attacker knowledge theorem,
///   proving that each function preserves publishability
/// - lemmas for the user on honest usage of cryptography,
///   stating and proving under which condition functions preserve the bytes invariant
/// - other lemmas that can be useful, such as lemmas on labels

/// Compute the length of a bytestring.
/// The output length of various cryptographic function is guessed to be some specific (realistic) value,
/// this handling could be improved but is good enough.
/// Such a length function is crucial to integrate DY* with Comparse.

[@@"opaque_to_smt"]
val length: bytes -> nat
let rec length b =
  match b with
  | Literal buf ->
    Seq.length buf
  | Rand usg label len time ->
    len
  | Concat left right ->
    length left + length right
  | AeadEnc key nonce msg ad ->
    16 + length msg
  | Pk sk ->
    32
  | PkEnc pk nonce msg ->
    64 + length msg
  | Vk sk ->
    32
  | Sign sk nonce msg ->
    64
  | Hash msg ->
    32
  | DhPub sk ->
    32
  | Dh sk pk ->
    32
  | KdfExtract salt ikm ->
    32
  | KdfExpand prk info len ->
    len
  | KemPub sk ->
    32
  | KemEncap pk nonce ->
    32
  | KemSecretShared nonce ->
    32

/// Customizable functions stating how labels and usages evolve
/// when using some cryptographic functions.

noeq
type dh_crypto_usage = {
  known_peer_usage: usg1:usage{DhKey? usg1} -> usg2:usage{DhKey? usg2} -> usage;
  unknown_peer_usage: usg:usage{DhKey? usg} -> usage;
  known_peer_usage_commutes:
    usg1:usage{DhKey? usg1} -> usg2:usage{DhKey? usg2} -> Lemma
    (known_peer_usage usg1 usg2 == known_peer_usage usg2 usg1)
  ;
  unknown_peer_usage_implies:
    usg1:usage{DhKey? usg1} -> usg2:usage{DhKey? usg2} -> Lemma
    (requires unknown_peer_usage usg1 =!= NoUsage)
    (ensures known_peer_usage usg1 usg2 == unknown_peer_usage usg1)
  ;
}


noeq
type kdf_extract_crypto_usage = {
  /// HKDF.Extract is commonly used as a dual-PRF to mix two secrets keys,
  /// thereby obtaining a new key that is as strong as the strongest input key.
  /// This nature of being a dual-PRF means that one of the inputs must have the correct usage,
  /// but we don't know statically which one.
  /// This explains the "or" in the preconditions.

  /// The usage of HKDF.Extract depends on both the usage and the content of its inputs.
  get_usage:
    salt_usage:usage -> ikm_usage:usage ->
    salt:bytes -> ikm:bytes ->
    Pure usage (requires KdfExtractSaltKey? salt_usage \/ KdfExtractIkmKey? ikm_usage) (ensures fun _ -> True)
  ;

  /// The label of HKDF.Extract depends on the usage, the label and the content of its inputs.
  get_label:
    salt_usage:usage -> ikm_usage:usage ->
    salt_label:label -> ikm_label:label ->
    salt:bytes -> ikm:bytes ->
    Pure label (requires KdfExtractSaltKey? salt_usage \/ KdfExtractIkmKey? ikm_usage) (ensures fun _ -> True)
  ;

  /// The label of HKDF.Extract cannot be too secret.
  get_label_lemma:
    tr:trace ->
    salt_usage:usage -> ikm_usage:usage ->
    salt_label:label -> ikm_label:label ->
    salt:bytes -> ikm:bytes ->
    Lemma
    (requires KdfExtractSaltKey? salt_usage \/ KdfExtractIkmKey? ikm_usage)
    (ensures (get_label salt_usage ikm_usage salt_label ikm_label salt ikm) `can_flow tr` (salt_label `meet` ikm_label))
  ;
}

noeq
type kdf_expand_crypto_usage = {
  /// HKDF.Expand is a more standard PRF to derive several keys from an initial one,
  /// therefore we know that `prk` must have the correct usage.
  /// In particular, it cannot be used to mix two secrets.
  /// Note that the usage and the label do not depend on the `len` argument,
  /// because `HKDF.Expand prk info len` is a prefix of `HKDF.Expand prk info (len+k)`.

  /// The usage of HKDF.Expand depends on the prk usage and the info content.
  get_usage:
    prk_usage:usage{KdfExpandKey? prk_usage} ->
    info:bytes ->
    usage;

  /// The label of HKDF.Expand depends on the prk usage and label and the info content.
  get_label:
    prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label ->
    info:bytes ->
    label;

  /// The label of HKDF.Expand cannot be too secret.
  get_label_lemma:
    tr:trace ->
    prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label ->
    info:bytes ->
    Lemma ((get_label prk_usage prk_label info) `can_flow tr` prk_label)
  ;
}

class crypto_usages = {
  dh_usage: dh_crypto_usage;
  kdf_extract_usage: kdf_extract_crypto_usage;
  kdf_expand_usage: kdf_expand_crypto_usage;
}

/// Default (empty) usage functions, that can be used like this:
/// { default_crypto_usages with ... }

val default_dh_crypto_usage: dh_crypto_usage
let default_dh_crypto_usage = {
  known_peer_usage = (fun s1 s2 -> NoUsage);
  unknown_peer_usage = (fun s1 -> NoUsage);
  known_peer_usage_commutes = (fun s1 s2 -> ());
  unknown_peer_usage_implies = (fun s1 s2 -> ());
}

val default_kdf_extract_crypto_usage: kdf_extract_crypto_usage
let default_kdf_extract_crypto_usage = {
  get_usage = (fun salt_usg ikm_usg salt ikm -> NoUsage);
  get_label = (fun salt_usg ikm_usg salt_label ikm_label salt ikm -> salt_label `meet` ikm_label);
  get_label_lemma = (fun tr salt_usg ikm_usg salt_label ikm_label salt ikm -> ());
}

val default_kdf_expand_crypto_usage: kdf_expand_crypto_usage
let default_kdf_expand_crypto_usage = {
  get_usage = (fun prk_usage info -> NoUsage);
  get_label = (fun prk_usage prk_label info -> prk_label);
  get_label_lemma = (fun tr prk_usage prk_label info -> ());
}

val default_crypto_usages: crypto_usages
let default_crypto_usages = {
  dh_usage = default_dh_crypto_usage;
  kdf_extract_usage = default_kdf_extract_crypto_usage;
  kdf_expand_usage = default_kdf_expand_crypto_usage;
}

/// Obtain the usage of a given bytestring.
/// See DY.Core.Bytes.Type for more explanations.

#push-options "--ifuel 2"
[@@"opaque_to_smt"]
val get_usage: {|crypto_usages|} -> b:bytes -> usage
let rec get_usage #cusages b =
  match b with
  | Rand usg label len time ->
    usg
  | Dh sk1 (DhPub sk2) -> (
    match get_usage sk1, get_usage sk2 with
    | DhKey _ _, DhKey _ _ ->
      dh_usage.known_peer_usage (get_usage sk1) (get_usage sk2)
    | DhKey _ _, _ ->
      dh_usage.unknown_peer_usage (get_usage sk1)
    | _, DhKey _ _ ->
      dh_usage.unknown_peer_usage (get_usage sk2)
    | _, _ ->
      NoUsage
  )
  | Dh sk pk -> (
    match get_usage sk with
    | DhKey _ _ -> dh_usage.unknown_peer_usage (get_usage sk)
    | _ -> NoUsage
  )
  | KdfExtract salt ikm -> (
    let salt_usage = get_usage salt in
    let ikm_usage = get_usage ikm in
    if KdfExtractSaltKey? salt_usage || KdfExtractIkmKey? ikm_usage then
      kdf_extract_usage.get_usage salt_usage ikm_usage salt ikm
    else
      NoUsage
  )
  | KdfExpand prk info len -> (
    let prk_usage = get_usage prk in
    if KdfExpandKey? prk_usage then
      kdf_expand_usage.get_usage prk_usage info
    else
      NoUsage
  )
  | KemSecretShared nonce -> (
    match get_usage nonce with
    | KemNonce usg -> usg
    | _ -> NoUsage
  )
  | _ -> NoUsage
#pop-options

/// Obtain the label of a given bytestring.

#push-options "--ifuel 2"
[@@"opaque_to_smt"]
val get_label: {|crypto_usages|} -> bytes -> label
let rec get_label #cusages b =
  match b with
  | Literal buf ->
    public
  | Rand usg label len time ->
    label
  | Concat left right ->
    meet (get_label left) (get_label right)
  | AeadEnc key nonce msg ad ->
    public
  | Pk sk ->
    public
  | PkEnc pk nonce msg ->
    public
  | Vk sk ->
    public
  | Sign sk nonce msg ->
    get_label msg
  | Hash msg ->
    get_label msg
  | DhPub sk ->
    public
  | Dh sk1 (DhPub sk2) ->
    join (get_label sk1) (get_label sk2)
  | Dh sk pk ->
    public
  | KdfExtract salt ikm ->
    let salt_usage = get_usage salt in
    let ikm_usage = get_usage ikm in
    if KdfExtractSaltKey? salt_usage || KdfExtractIkmKey? ikm_usage then
      kdf_extract_usage.get_label salt_usage ikm_usage (get_label salt) (get_label ikm) salt ikm
    else
      meet (get_label salt) (get_label ikm)
  | KdfExpand prk info len -> (
    let prk_usage = get_usage prk in
    if KdfExpandKey? prk_usage then
      kdf_expand_usage.get_label prk_usage (get_label prk) info
    else
      get_label prk
  )
  | KemPub sk ->
    public
  | KemEncap pk nonce ->
    public
  | KemSecretShared nonce ->
    get_label nonce
#pop-options

/// Obtain the label of the corresponding decryption key of an encryption key.
/// Although the encryption key label is public,
/// this is useful to reason on the corresponding decryption key label.

[@@"opaque_to_smt"]
val get_sk_label: {|crypto_usages|} -> bytes -> label
let get_sk_label #cusages pk =
  match pk with
  | Pk sk -> get_label sk
  | _ -> public

/// Same as above, for usage.

[@@"opaque_to_smt"]
val get_sk_usage: {|crypto_usages|} -> bytes -> usage
let get_sk_usage #cusages pk =
  match pk with
  | Pk sk -> get_usage sk
  | _ -> NoUsage

/// Obtain the label of the corresponding signature key of a verification key.
/// Although the verification key label is public,
/// this is useful to reason on the corresponding signature key label.

[@@"opaque_to_smt"]
val get_signkey_label: {|crypto_usages|} -> bytes -> label
let get_signkey_label #cusages pk =
  match pk with
  | Vk sk -> get_label sk
  | _ -> public

/// Same as above, for usage.

[@@"opaque_to_smt"]
val get_signkey_usage: {|crypto_usages|} -> bytes -> usage
let get_signkey_usage #cusages pk =
  match pk with
  | Vk sk -> get_usage sk
  | _ -> NoUsage

/// Obtain the label of the corresponding DH private key of a DH public key.
/// Although the DH public key label is public,
/// this is useful to reason on the corresponding DH private key label.

[@@"opaque_to_smt"]
val get_dh_label: {|crypto_usages|} -> bytes -> label
let get_dh_label #cusages pk =
  match pk with
  | DhPub sk -> get_label sk
  | _ -> public

/// Same as above, for usage.

[@@"opaque_to_smt"]
val get_dh_usage: {|crypto_usages|} -> bytes -> usage
let get_dh_usage #cusages pk =
  match pk with
  | DhPub sk -> get_usage sk
  | _ -> NoUsage

/// Obtain the label of the corresponding KEM private key of a KEM public key.
/// Although the KEM public key label is public,
/// this is useful to reason on the corresponding KEM private key label.

[@@"opaque_to_smt"]
val get_kem_sk_label: {|crypto_usages|} -> bytes -> label
let get_kem_sk_label #cusages pk =
  match pk with
  | KemPub sk -> get_label sk
  | _ -> public

/// Same as above, for usage.

[@@"opaque_to_smt"]
val get_kem_sk_usage: {|crypto_usages|} -> bytes -> usage
let get_kem_sk_usage #cusages pk =
  match pk with
  | KemPub sk -> get_usage sk
  | _ -> NoUsage


/// Customizable predicates stating how cryptographic functions may be used
/// by honest principals.

noeq
type aead_crypto_predicate (cusages:crypto_usages) = {
  pred: tr:trace -> key:bytes{AeadKey? (get_usage key)} -> nonce:bytes -> msg:bytes -> ad:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    key:bytes{AeadKey? (get_usage key)} -> nonce:bytes -> msg:bytes -> ad:bytes ->
    Lemma
    (requires pred tr1 key nonce msg ad /\ tr1 <$ tr2)
    (ensures pred tr2 key nonce msg ad)
  ;
}

noeq
type pkenc_crypto_predicate (cusages:crypto_usages) = {
  pred: tr:trace -> pk:bytes{PkKey? (get_sk_usage pk)} -> msg:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    pk:bytes{PkKey? (get_sk_usage pk)} -> msg:bytes ->
    Lemma
    (requires pred tr1 pk msg /\ tr1 <$ tr2)
    (ensures pred tr2 pk msg)
  ;
}

noeq
type sign_crypto_predicate (cusages:crypto_usages) = {
  pred: tr:trace -> vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes ->
    Lemma
    (requires pred tr1 vk msg /\ tr1 <$ tr2)
    (ensures pred tr2 vk msg)
  ;
}

noeq
type crypto_predicates (cusages:crypto_usages) = {
  aead_pred: aead_crypto_predicate cusages;
  pkenc_pred: pkenc_crypto_predicate cusages;
  sign_pred: sign_crypto_predicate cusages;
}

/// Default (empty) cryptographic predicates, that can be used like this:
/// { default_crypto_predicates with
///   sign_pred = ...;
/// }

val default_aead_predicate: cusages:crypto_usages -> aead_crypto_predicate cusages
let default_aead_predicate cusages = {
  pred = (fun tr key nonce msg ad -> False);
  pred_later = (fun tr1 tr2 key nonce msg ad -> ());
}

val default_pkenc_predicate: cusages:crypto_usages -> pkenc_crypto_predicate cusages
let default_pkenc_predicate cusages = {
  pred = (fun tr pk msg -> False);
  pred_later = (fun tr1 tr2 pk msg -> ());
}

val default_sign_predicate: cusages:crypto_usages -> sign_crypto_predicate cusages
let default_sign_predicate cusages = {
  pred = (fun tr vk msg -> False);
  pred_later = (fun tr1 tr2 vk msg -> ());
}

val default_crypto_predicates:
  cusages:crypto_usages ->
  crypto_predicates cusages
let default_crypto_predicates cusages = {
  aead_pred = default_aead_predicate cusages;
  pkenc_pred = default_pkenc_predicate cusages;
  sign_pred = default_sign_predicate cusages;
}

/// Gather the usage functions and the cryptographic predicates
/// to obtain the cryptographic invariants,
/// which will be a parameter of the bytes invariant.

class crypto_invariants = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  usages: crypto_usages;
  [@@@FStar.Tactics.Typeclasses.no_method]
  preds: crypto_predicates usages;
}

// `crypto_predicates` cannot be a typeclass that is inherited by `crypto_invariants`,
// hence we simulate inheritance like this.

let aead_pred {|cinvs:crypto_invariants|} = cinvs.preds.aead_pred
let pkenc_pred {|cinvs:crypto_invariants|} = cinvs.preds.pkenc_pred
let sign_pred {|cinvs:crypto_invariants|} = cinvs.preds.sign_pred

/// The invariants on every bytestring used in a protocol execution.
/// - it is preserved by every honest participant
///   (this is something that is proved on a protocol analyzed with DY*)
/// - it is preserved by the attacker
///   (which preserve a stronger invariant, publishability, proved in DY.Core.Attacker.Knowledge).

[@@"opaque_to_smt"]
val bytes_invariant: {|crypto_invariants|} -> trace -> bytes -> prop
let rec bytes_invariant #cinvs tr b =
  match b with
  | Literal buf ->
    True
  | Rand usage label len time ->
    // Random bytes correspond to an event
    event_at tr time (RandGen usage label len)
  | Concat left right ->
    bytes_invariant tr left /\
    bytes_invariant tr right
  | AeadEnc key nonce msg ad ->
    bytes_invariant tr key /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    bytes_invariant tr ad /\
    // the nonce is a public value
    // (e.g. it is often transmitted on the network)
    (get_label nonce) `can_flow tr` public /\
    // the standard IND-CCA assumption do not guarantee indistinguishability of additional data,
    // hence it must flow to public
    (get_label ad) `can_flow tr` public /\
    (
      (
        // Honest case:
        // - the key has the usage of AEAD key
        AeadKey? (get_usage key) /\
        // - the custom (protocol-specific) invariant hold (authentication)
        aead_pred.pred tr key nonce msg ad /\
        // - the message is less secret than the key
        //   (this is crucial so that decryption preserve publishability)
        (get_label msg) `can_flow tr` (get_label key)
      ) \/ (
        // Attacker case:
        // the key and message are both public
        (get_label key) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Pk sk ->
    bytes_invariant tr sk
  | PkEnc pk nonce msg ->
    bytes_invariant tr pk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    (
      (
        // Honest case:
        // - the key has the usage of asymetric encryption key
        PkKey? (get_sk_usage pk) /\
        // - the custom (protocol-specific) invariant hold (authentication)
        pkenc_pred.pred tr pk msg /\
        // - the message is less secret than the decryption key
        //   (this is crucial so that decryption preserve publishability)
        (get_label msg) `can_flow tr` (get_sk_label pk) /\
        // - the message is less secret than the nonce
        //   (this is because the standard IND-CCA security assumption
        //   do not give guarantees on the indistinguishability of the message
        //   when the attacker knows the nonce)
        (get_label msg) `can_flow tr` (get_label nonce) /\
        // - the nonce has the correct usage (for the same reason as above)
        PkNonce? (get_usage nonce)
      ) \/ (
        // Attacker case:
        // the attacker knows the nonce, key and message
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Vk sk ->
    bytes_invariant tr sk
  | Sign sk nonce msg ->
    bytes_invariant tr sk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    (
      (
        // Honest case:
        // - the key has the usage of signature key
        SigKey? (get_signkey_usage (Vk sk)) /\
        // - the custom (protocol-specific) invariant hold (authentication)
        sign_pred.pred tr (Vk sk) msg /\
        // - the nonce is more secret than the signature key
        //   (this is because the standard EUF-CMA security assumption on signatures
        //   do not have any guarantees when the nonce is leaked to the attacker,
        //   in practice knowing the nonce used to sign a message
        //   can be used to obtain the private key,
        //   hence this restriction)
        (get_label sk) `can_flow tr` (get_label nonce) /\
        // - the nonce has the correct usage (for the same reason as above)
        SigNonce? (get_usage nonce)
      ) \/ (
        // Attacker case:
        // the attacker knows the signature key, nonce and message
        (get_label sk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Hash msg ->
    bytes_invariant tr msg
  | DhPub sk ->
    bytes_invariant tr sk
  | Dh sk1 (DhPub sk2) ->
    bytes_invariant tr sk1 /\
    bytes_invariant tr sk2 /\
    (
      (
        // Honest case:
        // - one of the keys have the correct usage
        DhKey? (get_usage sk1) \/
        DhKey? (get_usage sk2)
      ) \/ (
        // Attacker case:
        // the attacker knows one of the secret keys
        (get_label sk1) `can_flow tr` public \/
        (get_label sk2) `can_flow tr` public
      )
    )
  | Dh sk pk ->
    bytes_invariant tr pk /\
    bytes_invariant tr sk /\
    (get_label pk) `can_flow tr` public /\
    (
      (
        DhKey? (get_usage sk)
      ) \/ (
        (get_label sk) `can_flow tr` public
      )
    )
  | KdfExtract salt ikm ->
    bytes_invariant tr salt /\
    bytes_invariant tr ikm /\
    (
      (
        // Honest case:
        // either salt or ikm has the correct usage
        // (this is to model the extract function as a dual PRF)
        KdfExtractSaltKey? (get_usage salt) \/
        KdfExtractIkmKey? (get_usage ikm)
      ) \/ (
        // Attacker case:
        // the attacker knows both salt and ikm
        (get_label salt) `can_flow tr` public /\
        (get_label ikm) `can_flow tr` public
      )
    )
  | KdfExpand prk info len ->
    bytes_invariant tr prk /\
    bytes_invariant tr info /\
    (
      (
        // Honest case:
        // the prk has correct usage
        KdfExpandKey? (get_usage prk)
      ) \/ (
        // Attacker case:
        // the attacker knows both prk and info
        (get_label prk) `can_flow tr` public
      )
    )
  | KemPub sk ->
    bytes_invariant tr sk
  | KemEncap pk nonce ->
    bytes_invariant tr pk /\
    bytes_invariant tr nonce /\
    (
      (
        // Honest case:
        // nonce is knowable by the holder of pk
        // (because the nonce roughly corresponds to the shared secret)
        (get_label nonce) `can_flow tr` (get_kem_sk_label pk) /\ (
        // nonce and pk agree on the usage of the shared secret
        // (this is because this KEM model does not bind the public key to the shared secret)
          match get_kem_sk_usage pk, get_usage nonce with
          | KemKey usg_key, KemNonce usg_nonce ->
            usg_key == usg_nonce
          | _, _ -> False
        )
      ) \/ (
        // Attacker case:
        // the attacker knows both pk and nonce
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public
      )
    )
  | KemSecretShared nonce ->
    bytes_invariant tr nonce


/// The bytes invariant is preserved as the trace grows.

val bytes_invariant_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace -> msg:bytes ->
  Lemma
  (requires bytes_invariant tr1 msg /\ tr1 <$ tr2)
  (ensures bytes_invariant tr2 msg)
  [SMTPat (bytes_invariant tr1 msg); SMTPat (tr1 <$ tr2)]
let rec bytes_invariant_later #cinvs tr1 tr2 msg =
  normalize_term_spec bytes_invariant;
  match msg with
  | Literal buf -> ()
  | Rand usage label len time -> ()
  | Concat left right ->
    bytes_invariant_later tr1 tr2 left;
    bytes_invariant_later tr1 tr2 right
  | AeadEnc key nonce msg ad -> (
    bytes_invariant_later tr1 tr2 key;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    bytes_invariant_later tr1 tr2 ad;
    match get_usage key with
    | AeadKey _ _ -> FStar.Classical.move_requires (aead_pred.pred_later tr1 tr2 key nonce msg) ad
    | _ -> ()
  )
  | Pk sk ->
    bytes_invariant_later tr1 tr2 sk
  | PkEnc pk nonce msg -> (
    bytes_invariant_later tr1 tr2 pk;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    match get_sk_usage pk with
    | PkKey _ _ -> FStar.Classical.move_requires (cinvs.preds.pkenc_pred.pred_later tr1 tr2 pk) msg
    | _ -> ()
  )
  | Vk sk ->
    bytes_invariant_later tr1 tr2 sk
  | Sign sk nonce msg -> (
    bytes_invariant_later tr1 tr2 sk;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    match get_signkey_usage (Vk sk) with
    | SigKey _ _ -> FStar.Classical.move_requires (cinvs.preds.sign_pred.pred_later tr1 tr2 (Vk sk)) msg
    | _ -> ()
  )
  | Hash msg ->
    bytes_invariant_later tr1 tr2 msg
  | DhPub sk ->
    bytes_invariant_later tr1 tr2 sk
  | Dh sk1 (DhPub sk2) ->
    bytes_invariant_later tr1 tr2 sk1;
    bytes_invariant_later tr1 tr2 sk2
  | Dh sk pk ->
    bytes_invariant_later tr1 tr2 pk;
    bytes_invariant_later tr1 tr2 sk
  | KdfExtract salt ikm ->
    bytes_invariant_later tr1 tr2 salt;
    bytes_invariant_later tr1 tr2 ikm
  | KdfExpand prk info len ->
    bytes_invariant_later tr1 tr2 prk;
    bytes_invariant_later tr1 tr2 info
  | KemPub sk ->
    bytes_invariant_later tr1 tr2 sk
  | KemEncap pk nonce ->
    bytes_invariant_later tr1 tr2 pk;
    bytes_invariant_later tr1 tr2 nonce
  | KemSecretShared nonce ->
    bytes_invariant_later tr1 tr2 nonce

(*** Various predicates ***)

/// Below are a few shorthand predicates on bytes,
/// that are derived from bytes invariant, label and usage.
/// They capture common properties we use to reason on bytestrings.
/// They are not opaque to SMT because users have to reason with their definitions.

/// Is a given bytestring less secret than a given label?
/// In other words, can the bytestring be known to principals captured by this label?

val is_knowable_by: {|crypto_invariants|} -> label -> trace -> bytes -> prop
let is_knowable_by #cinvs lab tr b =
  bytes_invariant tr b /\ (get_label b) `can_flow tr` lab

/// Particular case of the above predicate:
/// can a given bytestring be published (e.g. on the network)?
/// This predicate is will be used to define the attacker knowledge theorem
/// (see DY.Core.Attacker.Knowledge).

val is_publishable: {|crypto_invariants|} -> trace -> bytes -> prop
let is_publishable #cinvs tr b =
  is_knowable_by public tr b

/// Is a given bytestring secret, with some specific label?

val is_secret: {|crypto_invariants|} -> label -> trace -> bytes -> prop
let is_secret #cinvs lab tr b =
  bytes_invariant tr b /\ (get_label b) == lab

/// Shorthand predicates for the various type of keys.

val is_verification_key: {|crypto_invariants|} -> usg:usage{SigKey? usg} -> label -> trace -> bytes -> prop
let is_verification_key #cinvs usg lab tr b =
  is_publishable tr b /\ (get_signkey_label b) == lab /\
  get_signkey_usage b == usg

val is_signature_key: {|crypto_invariants|} -> usg:usage{SigKey? usg} -> label -> trace -> bytes -> prop
let is_signature_key #cinvs usg lab tr b =
  is_secret lab tr b /\
  get_usage b == usg

val is_encryption_key: {|crypto_invariants|} -> usg:usage{PkKey? usg} -> label -> trace -> bytes -> prop
let is_encryption_key #cinvs usg lab tr b =
  is_publishable tr b /\ (get_sk_label b) == lab /\
  get_sk_usage b == usg

val is_decryption_key: {|crypto_invariants|} -> usg:usage{PkKey? usg} -> label -> trace -> bytes -> prop
let is_decryption_key #cinvs usg lab tr b =
  is_secret lab tr b /\
  get_usage b == usg

(*** Literal ***)

/// Constructor.

[@@"opaque_to_smt"]
val literal_to_bytes: FStar.Seq.seq FStar.UInt8.t -> bytes
let literal_to_bytes lit =
  Literal lit

/// Destructor.

[@@"opaque_to_smt"]
val bytes_to_literal: bytes -> option (FStar.Seq.seq FStar.UInt8.t)
let bytes_to_literal msg =
  match msg with
  | Literal lit -> Some lit
  | _ -> None

/// Symbolic reduction rules.

val literal_to_bytes_to_literal:
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (bytes_to_literal (literal_to_bytes lit) == Some lit)
let literal_to_bytes_to_literal lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_to_literal

/// Lemma for attacker knowledge theorem.

val literal_to_bytes_is_publishable:
  {|crypto_invariants|} -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (is_publishable tr (literal_to_bytes lit))
let literal_to_bytes_is_publishable #cinvs tr lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (back-and-forth)

val bytes_to_literal_to_bytes:
  b:bytes ->
  Lemma (
    match bytes_to_literal b with
    | None -> True
    | Some lit -> b == literal_to_bytes lit
  )
let bytes_to_literal_to_bytes b =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_to_literal


/// User lemma (length).

val length_literal_to_bytes:
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma (length (literal_to_bytes lit) == FStar.Seq.length lit)
  [SMTPat (length (literal_to_bytes lit))]
let length_literal_to_bytes lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec length

/// User lemma (bytes invariant).
/// Coincidentally this is the same as the attacker knowledge lemma above,
/// but with an SMT pattern.

val bytes_invariant_literal_to_bytes:
  {|crypto_invariants|} -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (ensures is_publishable tr (literal_to_bytes lit))
  [SMTPat (bytes_invariant tr (literal_to_bytes lit))]
let bytes_invariant_literal_to_bytes #cinvs tr lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

(*** Concatenation ***)

/// Constructor.

[@@"opaque_to_smt"]
val concat: bytes -> bytes -> bytes
let concat left right =
  Concat left right

/// Destructor.
/// Splitting returns an option,
/// for example if the spliting index is out-of-bound.
/// Here, we additionnally fail if the splitting is not done at the boundary of a concatenation.
/// For example, we cannot split in the middle of a ciphertext.

[@@"opaque_to_smt"]
val split: bytes -> nat -> option (bytes & bytes)
let split b i =
  match b with
  | Concat left right ->
    if length left = i then
      Some (left, right)
    else
      None
  | _ -> None

/// Symbolic reduction rule.

val split_concat:
  left:bytes -> right:bytes ->
  Lemma
  (split (concat left right) (length left) == Some (left, right))
let split_concat left right =
  normalize_term_spec split;
  normalize_term_spec concat

/// Lemma for attacker knowledge theorem.

val concat_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (requires is_publishable tr b1 /\ is_publishable tr b2)
  (ensures is_publishable tr (concat b1 b2))
let concat_preserves_publishability #cinvs tr b1 b2 =
  normalize_term_spec concat;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// Lemma for attacker knowledge theorem.

val split_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  b:bytes -> i:nat ->
  Lemma
  (requires is_publishable tr b)
  (ensures (
    match split b i with
    | None -> True
    | Some (b1, b2) -> is_publishable tr b1 /\ is_publishable tr b2
  ))
let split_preserves_publishability #cinvs tr b i =
  normalize_term_spec split;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (back-and-forth).

val concat_split:
  b:bytes -> i:nat ->
  Lemma (
    match split b i with
    | None -> True
    | Some (left, right) -> b == concat left right
  )
let concat_split b i =
  normalize_term_spec concat;
  normalize_term_spec split

/// User lemma (concatenation length).

val concat_length:
  left:bytes -> right:bytes ->
  Lemma
  (length (concat left right) = length left + length right)
let concat_length left right =
  normalize_term_spec concat;
  normalize_term_spec length

/// User lemma (splitting length).

val split_length:
  b:bytes -> i:nat ->
  Lemma (
    match split b i with
    | None -> True
    | Some (b1, b2) -> length b1 == i /\ i + length b2 == length b
  )
let split_length b i =
  normalize_term_spec split;
  normalize_term_spec length

/// User lemma (concatenation bytes invariant).

val bytes_invariant_concat:
  {|crypto_invariants|} -> tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (requires bytes_invariant tr b1 /\ bytes_invariant tr b2)
  (ensures bytes_invariant tr (concat b1 b2))
  [SMTPat (bytes_invariant tr (concat b1 b2))]
let bytes_invariant_concat #cinvs tr b1 b2 =
  normalize_term_spec concat;
  normalize_term_spec bytes_invariant

/// User lemma (splitting bytes invariant).

val bytes_invariant_split:
  {|crypto_invariants|} -> tr:trace ->
  b:bytes -> i:nat ->
  Lemma
  (requires bytes_invariant tr b)
  (ensures (
    match split b i with
    | None -> True
    | Some (b1, b2) -> bytes_invariant tr b1 /\ bytes_invariant tr b2
  ))
  [SMTPat (bytes_invariant tr b); SMTPat (split b i)]
let bytes_invariant_split #cinvs tr b i =
  normalize_term_spec split;
  normalize_term_spec bytes_invariant

/// User lemma (concatenation label).

val get_label_concat:
  {|crypto_usages|} ->
  b1:bytes -> b2:bytes ->
  Lemma
  (ensures get_label (concat b1 b2) == meet (get_label b1) (get_label b2))
  [SMTPat (get_label (concat b1 b2))]
let get_label_concat b1 b2 =
  normalize_term_spec concat;
  normalize_term_spec get_label

/// User lemma (concatenation knowability).

val concat_preserves_knowability:
  {|crypto_invariants|} -> lab:label -> tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (requires is_knowable_by lab tr b1 /\ is_knowable_by lab tr b2)
  (ensures is_knowable_by lab tr (concat b1 b2))
  [SMTPat (is_knowable_by lab tr (concat b1 b2))]
let concat_preserves_knowability #cinvs lab tr b1 b2 =
  normalize_term_spec concat;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (splitting knowability).

val split_preserves_knowability:
  {|crypto_invariants|} -> lab:label -> tr:trace ->
  b:bytes -> i:nat ->
  Lemma
  (requires is_knowable_by lab tr b)
  (ensures (
    match split b i with
    | None -> True
    | Some (b1, b2) -> is_knowable_by lab tr b1 /\ is_knowable_by lab tr b2
  ))
let split_preserves_knowability #cinvs lab tr b i =
  normalize_term_spec split;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

(*** AEAD ***)

/// Constructor.

[@@"opaque_to_smt"]
val aead_enc: bytes -> bytes -> bytes -> bytes -> bytes
let aead_enc key nonce msg ad =
  AeadEnc key nonce msg ad

/// Destructor.

[@@"opaque_to_smt"]
val aead_dec: bytes -> bytes -> bytes -> bytes -> option bytes
let aead_dec key nonce msg ad =
  match msg with
  | AeadEnc key' nonce' res ad' ->
    if key = key' && nonce = nonce' && ad = ad' then
      Some res
    else
      None
  | _ -> None

/// Symbolic reduction rule.

val aead_dec_enc:
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (aead_dec key nonce (aead_enc key nonce msg ad) ad == Some msg)
let aead_dec_enc key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec aead_dec

/// Lemma for attacker knowledge theorem.

val aead_enc_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    is_publishable tr key /\
    is_publishable tr nonce /\
    is_publishable tr msg /\
    is_publishable tr ad
  )
  (ensures is_publishable tr (aead_enc key nonce msg ad))
let aead_enc_preserves_publishability #cinvs tr key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// Lemma for attacker knowledge theorem.

val aead_dec_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    is_publishable tr key /\
    is_publishable tr nonce /\
    is_publishable tr msg /\
    is_publishable tr ad
  )
  (ensures (
    match aead_dec key nonce msg ad with
    | Some res -> is_publishable tr res
    | None -> True
  ))
let aead_dec_preserves_publishability #cinvs tr key nonce msg ad =
  normalize_term_spec aead_dec;
  normalize_term_spec bytes_invariant;
  // F* needs the match for some reason,
  // see FStarLang/FStar#3093.
  match aead_dec key nonce msg ad with
  | Some res -> ()
  | None -> ()

/// User lemma (AEAD encryption bytes invariant).

val bytes_invariant_aead_enc:
  {|crypto_invariants|} -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    bytes_invariant tr key /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    bytes_invariant tr ad /\
    (get_label nonce) `can_flow tr` public /\
    (get_label ad) `can_flow tr` public /\
    (get_label msg) `can_flow tr` (get_label key) /\
    (AeadKey? (get_usage key) \/ get_label key `can_flow tr` public) /\
    ((get_label key `can_flow tr` public) \/ aead_pred.pred tr key nonce msg ad)
  )
  (ensures bytes_invariant tr (aead_enc key nonce msg ad))
  [SMTPat (bytes_invariant tr (aead_enc key nonce msg ad))]
let bytes_invariant_aead_enc #cinvs tr key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec bytes_invariant

/// User lemma (AEAD encryption label).

val get_label_aead_enc:
  {|crypto_usages|} ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (ensures get_label (aead_enc key nonce msg ad) = public)
  [SMTPat (get_label (aead_enc key nonce msg ad))]
let get_label_aead_enc #cusages key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec get_label

/// User lemma (AEAD decryption bytes invariant).

val bytes_invariant_aead_dec:
  {|crypto_invariants|} -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    // Actually only need the one on `msg`
    bytes_invariant tr key /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    bytes_invariant tr ad
  )
  (ensures (
    match aead_dec key nonce msg ad with
    | None -> True
    | Some plaintext -> (
      is_knowable_by (get_label key) tr plaintext /\
      (
        (
          AeadKey? (get_usage key) ==>
          aead_pred.pred tr key nonce plaintext ad
        ) \/ (
          is_publishable tr key
        )
      )
    )
  ))
  [SMTPat (aead_dec key nonce msg ad); SMTPat (bytes_invariant tr msg)]
let bytes_invariant_aead_dec #cinvs tr key nonce msg ad =
  normalize_term_spec aead_dec;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  match aead_dec key nonce msg ad with
  | None -> ()
  | Some msg -> ()

(*** Public-key encryption ***)

/// Constructor.

[@@"opaque_to_smt"]
val pk: bytes -> bytes
let pk sk = Pk sk

/// Constructor.

[@@"opaque_to_smt"]
val pk_enc: bytes -> bytes -> bytes -> bytes
let pk_enc pk nonce msg =
  PkEnc pk nonce msg

/// Destructor.

[@@"opaque_to_smt"]
val pk_dec: bytes -> bytes -> option bytes
let pk_dec sk msg =
  match msg with
  | PkEnc (Pk sk') nonce res ->
    if sk = sk' then
      Some res
    else
      None
  | _ -> None

/// Symbolic reduction rule.

val pk_dec_enc:
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (pk_dec sk (pk_enc (pk sk) nonce msg) == Some msg)
let pk_dec_enc key nonce msg =
  normalize_term_spec pk_dec;
  normalize_term_spec pk_enc;
  normalize_term_spec pk

/// Lemma for attacker knowledge theorem.

val pk_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable tr sk)
  (ensures is_publishable tr (pk sk))
let pk_preserves_publishability #cinvs tr sk =
  normalize_term_spec pk;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// Lemma for attacker knowledge theorem.

val pk_enc_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable tr pk /\
    is_publishable tr nonce /\
    is_publishable tr msg
  )
  (ensures is_publishable tr (pk_enc pk nonce msg))
let pk_enc_preserves_publishability #cinvs tr pk nonce msg =
  normalize_term_spec pk_enc;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// Lemma for attacker knowledge theorem.

#push-options "--z3rlimit 25"
val pk_dec_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable tr sk /\
    is_publishable tr msg
  )
  (ensures (
    match pk_dec sk msg with
    | Some res -> is_publishable tr res
    | None -> True
  ))
let pk_dec_preserves_publishability #cinvs tr sk msg =
  normalize_term_spec pk_dec;
  normalize_term_spec get_sk_label;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label
#pop-options

/// User lemma (public encryption key bytes invariant).

val bytes_invariant_pk:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant tr sk)
  (ensures bytes_invariant tr (pk sk))
  [SMTPat (bytes_invariant tr (pk sk))]
let bytes_invariant_pk #cinvs tr sk =
  normalize_term_spec pk;
  normalize_term_spec bytes_invariant

/// User lemma (public encryption key label).

val get_label_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_label (pk sk) == public)
  [SMTPat (get_label (pk sk))]
let get_label_pk #cusages sk =
  normalize_term_spec pk;
  normalize_term_spec get_label

/// User lemma (public encryption key sk label).

val get_sk_label_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_sk_label (pk sk) == get_label sk)
  [SMTPat (get_sk_label (pk sk))]
let get_sk_label_pk #cusages sk =
  normalize_term_spec pk;
  normalize_term_spec get_sk_label

/// User lemma (public encryption key sk usage).

val get_sk_usage_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_sk_usage (pk sk) == get_usage sk)
  [SMTPat (get_sk_usage (pk sk))]
let get_sk_usage_pk #cusages sk =
  normalize_term_spec pk;
  normalize_term_spec get_sk_usage

/// User lemma (public-key encryption bytes invariant).

val bytes_invariant_pk_enc:
  {|crypto_invariants|} -> tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant tr pk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    (get_label msg) `can_flow tr` (get_sk_label pk) /\
    (get_label msg) `can_flow tr` (get_label nonce) /\
    PkKey? (get_sk_usage pk) /\
    PkNonce? (get_usage nonce) /\
    pkenc_pred.pred tr pk msg
  )
  (ensures bytes_invariant tr (pk_enc pk nonce msg))
  [SMTPat (bytes_invariant tr (pk_enc pk nonce msg))]
let bytes_invariant_pk_enc #cinvs tr pk nonce msg =
  normalize_term_spec pk_enc;
  normalize_term_spec bytes_invariant

/// User lemma (public-key encryption label).

val get_label_pk_enc:
  {|crypto_usages|} ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label (pk_enc pk nonce msg) == public)
  [SMTPat (get_label (pk_enc pk nonce msg))]
let get_label_pk_enc #cusages pk nonce msg =
  normalize_term_spec pk_enc;
  normalize_term_spec get_label

/// User lemma (public-key decryption bytes invariant).

#push-options "--z3rlimit 25"
val bytes_invariant_pk_dec:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr msg
  )
  (ensures (
    match pk_dec sk msg with
    | None -> True
    | Some plaintext ->
      is_knowable_by (get_label sk) tr plaintext /\
      (
        (
          PkKey? (get_sk_usage (pk sk)) ==>
          pkenc_pred.pred tr (pk sk) plaintext
        ) \/ (
          is_publishable tr plaintext
        )
      )
  ))
  [SMTPat (pk_dec sk msg); SMTPat (bytes_invariant tr msg)]
let bytes_invariant_pk_dec #cinvs tr sk msg =
  normalize_term_spec pk_dec;
  normalize_term_spec pk;
  normalize_term_spec get_sk_label;
  normalize_term_spec get_label;
  normalize_term_spec bytes_invariant
#pop-options

(*** Signature ***)

/// Constructor.

[@@"opaque_to_smt"]
val vk: bytes -> bytes
let vk sk = Vk sk

/// Constructor.

[@@"opaque_to_smt"]
val sign: bytes -> bytes -> bytes -> bytes
let sign sk nonce msg =
  Sign sk nonce msg

/// Destructor.

[@@"opaque_to_smt"]
val verify: bytes -> bytes -> bytes -> bool
let verify vk msg signature =
  match signature with
  | Sign sk nonce msg' ->
    vk = Vk sk && msg = msg'
  | _ -> false

/// Symbolic reduction rule.

val verify_sign:
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (verify (vk sk) msg (sign sk nonce msg))
let verify_sign sk nonce msg =
  normalize_term_spec vk;
  normalize_term_spec verify;
  normalize_term_spec sign

/// Lemma for attacker knowledge theorem.

val vk_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable tr sk)
  (ensures is_publishable tr (vk sk))
let vk_preserves_publishability #cinvs tr sk =
  normalize_term_spec vk;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// Lemma for attacker knowledge theorem.

val sign_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable tr sk /\
    is_publishable tr nonce /\
    is_publishable tr msg
  )
  (ensures is_publishable tr (sign sk nonce msg))
let sign_preserves_publishability #cinvs tr sk nonce msg =
  normalize_term_spec sign;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (verification key bytes invariant).

val bytes_invariant_vk:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant tr sk)
  (ensures bytes_invariant tr (vk sk))
  [SMTPat (bytes_invariant tr (vk sk))]
let bytes_invariant_vk #cinvs tr sk =
  normalize_term_spec vk;
  normalize_term_spec bytes_invariant

/// User lemma (verification key label).

val get_label_vk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_label (vk sk) == public)
  [SMTPat (get_label (vk sk))]
let get_label_vk #cusages sk =
  normalize_term_spec vk;
  normalize_term_spec get_label

/// User lemma (verification key signkey label).

val get_signkey_label_vk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_signkey_label (vk sk) == get_label sk)
  [SMTPat (get_signkey_label (vk sk))]
let get_signkey_label_vk #cusages sk =
  normalize_term_spec vk;
  normalize_term_spec get_signkey_label

/// User lemma (verification key signkey usage).

val get_signkey_usage_vk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_signkey_usage (vk sk) == get_usage sk)
  [SMTPat (get_signkey_usage (vk sk))]
let get_signkey_usage_vk #cusages sk =
  normalize_term_spec vk;
  normalize_term_spec get_signkey_usage

/// User lemma (signature bytes invariant).

val bytes_invariant_sign:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    SigKey? (get_usage sk) /\
    SigNonce? (get_usage nonce) /\
    sign_pred.pred tr (vk sk) msg /\
    (get_label sk) `can_flow tr` (get_label nonce)
  )
  (ensures bytes_invariant tr (sign sk nonce msg))
  [SMTPat (bytes_invariant tr (sign sk nonce msg))]
let bytes_invariant_sign #cinvs tr sk nonce msg =
  normalize_term_spec sign;
  normalize_term_spec vk;
  normalize_term_spec bytes_invariant

/// User lemma (signature label).

val get_label_sign:
  {|crypto_usages|} ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label (sign sk nonce msg) == get_label msg)
  [SMTPat (get_label (sign sk nonce msg))]
let get_label_sign #cusages sk nonce msg =
  normalize_term_spec sign;
  normalize_term_spec get_label

/// User lemma (verification bytes invariant).

val bytes_invariant_verify:
  {|crypto_invariants|} -> tr:trace ->
  vk:bytes -> msg:bytes -> signature:bytes ->
  Lemma
  (requires
    bytes_invariant tr vk /\
    bytes_invariant tr msg /\
    bytes_invariant tr signature /\
    verify vk msg signature
  )
  (ensures
    (
      SigKey? (get_signkey_usage vk) ==>
      sign_pred.pred tr vk msg
    ) \/ (
      (get_signkey_label vk) `can_flow tr` public
    )
  )
  [SMTPat (verify vk msg signature); SMTPat (bytes_invariant tr signature)]
let bytes_invariant_verify #cinvs tr vk msg signature =
  normalize_term_spec verify;
  normalize_term_spec get_signkey_label;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

(*** Hash ***)

/// Constructor.

[@@"opaque_to_smt"]
val hash: bytes -> bytes
let hash msg = Hash msg

/// Lemma for attacker knowledge theorem.

val hash_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  msg:bytes ->
  Lemma
  (requires is_publishable tr msg)
  (ensures is_publishable tr (hash msg))
let hash_preserves_publishability #cinvs tr msg =
  normalize_term_spec hash;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (hash bytes invariant).

val bytes_invariant_hash:
  {|crypto_invariants|} -> tr:trace ->
  msg:bytes ->
  Lemma
  (requires bytes_invariant tr msg)
  (ensures bytes_invariant tr (hash msg))
  [SMTPat (hash msg); SMTPat (bytes_invariant tr msg)]
let bytes_invariant_hash #cinvs tr msg =
  normalize_term_spec hash;
  normalize_term_spec bytes_invariant

/// User lemma (hash label).

val get_label_hash:
  {|crypto_usages|} ->
  msg:bytes ->
  Lemma (get_label (hash msg) == get_label msg)
  [SMTPat (get_label (hash msg))]
let get_label_hash #cusages msg =
  normalize_term_spec hash;
  normalize_term_spec get_label

/// User lemma (hash collision-resistance).

val hash_injective:
  msg1:bytes -> msg2:bytes ->
  Lemma
  (requires hash msg1 == hash msg2)
  (ensures msg1 == msg2)
  // No SMTPat, call this manually because it's an important argument of the proof.
  // If this decision has to be revised, do not do [SMTPat (hash msg1); SMTPat (hash msg2)],
  // as this would lead to quadratic triggering.
  // Write it as a theorem like `inv_hash (hash msg) == Some msg`
  // with [SMTPat (hash msg)].
let hash_injective msg1 msg2 =
  normalize_term_spec hash

(*** Diffie-Hellman ***)

/// Constructor.

[@@"opaque_to_smt"]
val dh_pk: bytes -> bytes
let dh_pk sk =
  DhPub sk

/// Constructor.

[@@"opaque_to_smt"]
val dh: bytes -> bytes -> bytes
let dh sk pk =
  match pk with
  | DhPub sk2 ->
    if sk `DY.Core.Internal.Ord.is_less_than` sk2 then
      Dh sk (DhPub sk2)
    else
      Dh sk2 (DhPub sk)
  | _ ->
    Dh sk pk

/// Symbolic reduction rule.

val dh_shared_secret_lemma:
  x:bytes -> y:bytes ->
  Lemma (dh x (dh_pk y) == dh y (dh_pk x))
let dh_shared_secret_lemma x y =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  DY.Core.Internal.Ord.is_less_than_total x y;
  FStar.Classical.move_requires_2 DY.Core.Internal.Ord.is_less_than_antisym x y

/// Lemma for attacker knowledge theorem.

val dh_pk_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable tr sk)
  (ensures is_publishable tr (dh_pk sk))
let dh_pk_preserves_publishability tr sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// Lemma for attacker knowledge theorem.

val dh_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> pk:bytes ->
  Lemma
  (requires
    is_publishable tr sk /\
    is_publishable tr pk
  )
  (ensures is_publishable tr (dh sk pk))
let dh_preserves_publishability tr sk pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (dh_pk preserves bytes invariant)

val bytes_invariant_dh_pk:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant tr sk)
  (ensures bytes_invariant tr (dh_pk sk))
  [SMTPat (bytes_invariant tr (dh_pk sk))]
let bytes_invariant_dh_pk tr sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  normalize_term_spec bytes_invariant

/// User lemma (DH public key is public)

val get_label_dh_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_label (dh_pk sk) == public)
  [SMTPat (get_label (dh_pk sk))]
let get_label_dh_pk sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  normalize_term_spec get_label

/// User lemma (get_dh_label on DH public key ).

val get_dh_label_dh_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (get_dh_label (dh_pk sk) == get_label sk)
  [SMTPat (get_dh_label (dh_pk sk))]
let get_dh_label_dh_pk sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%get_dh_label) (get_dh_label)

/// User lemma (get_dh_usage on DH public key ).

val get_dh_usage_dh_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (get_dh_usage (dh_pk sk) == get_usage sk)
  [SMTPat (get_dh_usage (dh_pk sk))]
let get_dh_usage_dh_pk sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%get_dh_usage) (get_dh_usage)

/// User lemma (dh bytes invariant)

val bytes_invariant_dh:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> pk:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    DhKey? (get_usage sk) /\
    is_publishable tr pk
  )
  (ensures bytes_invariant tr (dh sk pk))
  [SMTPat (bytes_invariant tr (dh sk pk))]
let bytes_invariant_dh tr sk pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec bytes_invariant

/// User lemma (dh bytes label)

#push-options "--z3rlimit 25"
val get_label_dh:
  {|crypto_usages|} ->
  sk:bytes -> pk:bytes ->
  Lemma
  (ensures (get_label (dh sk pk)) `always_equivalent` ((get_label sk) `join` (get_dh_label pk)))
  [SMTPat (get_label (dh sk pk))]
let get_label_dh sk pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec get_dh_label;
  normalize_term_spec get_label;
  join_always_commutes (get_label sk) (get_dh_label pk)
#pop-options

/// User lemma (dh bytes usage with known peer)

val get_usage_dh_known_peer:
  {|crypto_usages|} ->
  sk:bytes -> pk:bytes ->
  Lemma
  (requires
    DhKey? (get_usage sk) /\
    DhKey? (get_dh_usage pk)
  )
  (ensures (
    get_usage (dh sk pk) == dh_usage.known_peer_usage (get_usage sk) (get_dh_usage pk)
  ))
  [SMTPat (get_usage (dh sk pk))]
let get_usage_dh_known_peer sk pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec get_dh_usage;
  normalize_term_spec get_usage;
  dh_usage.known_peer_usage_commutes (get_usage sk) (get_dh_usage pk)

/// User lemma (dh bytes usage with unknown peer)

val get_usage_dh_unknown_peer:
  {|crypto_usages|} ->
  sk:bytes -> pk:bytes ->
  Lemma
  (requires
    DhKey? (get_usage sk) /\
    dh_usage.unknown_peer_usage (get_usage sk) <> NoUsage
  )
  (ensures (
    get_usage (dh sk pk) == dh_usage.unknown_peer_usage (get_usage sk)
  ))
  [SMTPat (get_usage (dh sk pk))]
let get_usage_dh_unknown_peer sk pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec get_dh_usage;
  normalize_term_spec get_usage;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (dh_usage.unknown_peer_usage_implies (get_usage sk)))

(*** KDF ***)

/// Constructor.

[@@"opaque_to_smt"]
val kdf_extract: bytes -> bytes -> bytes
let kdf_extract salt ikm =
  KdfExtract salt ikm

/// Constructor.

[@@"opaque_to_smt"]
val kdf_expand: bytes -> bytes -> len:nat{len <> 0} -> bytes
let kdf_expand prk info len =
  KdfExpand prk info len

/// Lemma for attacker knowledge theorem.

val kdf_extract_preserves_publishability:
  {|crypto_invariants|} ->
  tr:trace ->
  salt:bytes -> ikm:bytes ->
  Lemma
  (requires
    is_publishable tr salt /\
    is_publishable tr ikm
  )
  (ensures is_publishable tr (kdf_extract salt ikm))
let kdf_extract_preserves_publishability tr salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  let salt_usage = get_usage salt in
  let ikm_usage = get_usage ikm in
  if KdfExtractSaltKey? salt_usage || KdfExtractIkmKey? ikm_usage then
    kdf_extract_usage.get_label_lemma tr salt_usage ikm_usage (get_label salt) (get_label ikm) salt ikm
  else ()

/// Lemma for attacker knowledge theorem.

val kdf_expand_preserves_publishability:
  {|crypto_invariants|} ->
  tr:trace ->
  prk:bytes -> info:bytes -> len:nat{len <> 0} ->
  Lemma
  (requires
    is_publishable tr prk /\
    is_publishable tr info
  )
  (ensures is_publishable tr (kdf_expand prk info len))
let kdf_expand_preserves_publishability tr prk info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  let prk_usage = get_usage prk in
  if KdfExpandKey? prk_usage then
    kdf_expand_usage.get_label_lemma tr prk_usage (get_label prk) info
  else ()

/// Lemma for attacker knowledge theorem.

val kdf_expand_shorter_preserves_publishability:
  {|crypto_invariants|} ->
  tr:trace ->
  prk:bytes -> info:bytes ->
  len1:nat{len1 <> 0} -> len2:nat{len2 <> 0} ->
  Lemma
  (requires
    len1 <= len2 /\
    is_publishable tr (kdf_expand prk info len2)
  )
  (ensures is_publishable tr (kdf_expand prk info len1))
let kdf_expand_shorter_preserves_publishability tr prk info len1 len2 =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (kdf_extract preserves bytes invariant)

val bytes_invariant_kdf_extract:
  {|crypto_invariants|} ->
  tr:trace ->
  salt:bytes -> ikm:bytes ->
  Lemma
  (requires
    bytes_invariant tr salt /\
    bytes_invariant tr ikm /\
    (KdfExtractSaltKey? (get_usage salt) \/ KdfExtractIkmKey? (get_usage ikm))
  )
  (ensures bytes_invariant tr (kdf_extract salt ikm))
  [SMTPat (bytes_invariant tr (kdf_extract salt ikm))]
let bytes_invariant_kdf_extract tr salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  normalize_term_spec bytes_invariant

/// User lemma (kdf_extract usage)

val get_usage_kdf_extract:
  {|crypto_invariants|} ->
  salt:bytes -> ikm:bytes ->
  Lemma
  (requires
    (KdfExtractSaltKey? (get_usage salt) \/ KdfExtractIkmKey? (get_usage ikm))
  )
  (ensures
    get_usage (kdf_extract salt ikm) ==
    kdf_extract_usage.get_usage
      (get_usage salt) (get_usage ikm)
      salt ikm
  )
  [SMTPat (get_usage (kdf_extract salt ikm))]
let get_usage_kdf_extract salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  normalize_term_spec get_usage

/// User lemma (kdf_extract label)

val get_label_kdf_extract:
  {|crypto_invariants|} ->
  salt:bytes -> ikm:bytes ->
  Lemma
  (requires
    (KdfExtractSaltKey? (get_usage salt) \/ KdfExtractIkmKey? (get_usage ikm))
  )
  (ensures
    get_label (kdf_extract salt ikm) ==
    kdf_extract_usage.get_label
      (get_usage salt) (get_usage ikm)
      (get_label salt) (get_label ikm)
      salt ikm
  )
  [SMTPat (get_label (kdf_extract salt ikm))]
let get_label_kdf_extract salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  normalize_term_spec get_label

/// User lemma (kdf_expand preserves bytes invariant)

val bytes_invariant_kdf_expand:
  {|crypto_invariants|} ->
  tr:trace ->
  prk:bytes -> info:bytes -> len:nat{len <> 0} ->
  Lemma
  (requires
    bytes_invariant tr prk /\
    bytes_invariant tr info /\
    (
      KdfExpandKey? (get_usage prk) \/
      get_label prk `can_flow tr` public
    )
  )
  (ensures bytes_invariant tr (kdf_expand prk info len))
  [SMTPat (bytes_invariant tr (kdf_expand prk info len))]
let bytes_invariant_kdf_expand tr prk info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec bytes_invariant

/// User lemma (kdf_expand usage)

val get_usage_kdf_expand:
  {|crypto_invariants|} ->
  prk:bytes -> info:bytes -> len:nat{len <> 0} ->
  Lemma
  (requires KdfExpandKey? (get_usage prk))
  (ensures (
    get_usage (kdf_expand prk info len) == kdf_expand_usage.get_usage (get_usage prk) info
  ))
  [SMTPat (get_usage (kdf_expand prk info len))]
let get_usage_kdf_expand prk info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec get_usage

/// User lemma (kdf_expand label)

val get_label_kdf_expand:
  {|crypto_invariants|} ->
  prk:bytes -> info:bytes -> len:nat{len <> 0} ->
  Lemma
  (requires KdfExpandKey? (get_usage prk))
  (ensures (
    get_label (kdf_expand prk info len) == kdf_expand_usage.get_label (get_usage prk) (get_label prk) info
  ))
  [SMTPat (get_label (kdf_expand prk info len))]
let get_label_kdf_expand prk info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec get_label

/// User lemma (kdf_expand label can flow)

val get_label_kdf_expand_can_flow:
  {|crypto_invariants|} ->
  tr:trace ->
  prk:bytes -> info:bytes -> len:nat{len <> 0} ->
  Lemma (get_label (kdf_expand prk info len) `can_flow tr` (get_label prk))
  [SMTPat (can_flow tr (get_label (kdf_expand prk info len)))]
let get_label_kdf_expand_can_flow tr prk info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec get_label;
  match get_usage prk with
  | KdfExpandKey _ _ ->
    kdf_expand_usage.get_label_lemma tr (get_usage prk) (get_label prk) info
  | _ -> ()

(*** KEM ***)

/// Constructor.

[@@"opaque_to_smt"]
val kem_pk: bytes -> bytes
let kem_pk sk =
  KemPub sk

/// Constructor.
///
/// Note that KemSecretShared does not include `pk`,
/// this is to model a KEM that does not bind the shared secret
/// to the public key.
/// See https://eprint.iacr.org/2023/1933 for more information

[@@"opaque_to_smt"]
val kem_encap: bytes -> bytes -> (bytes & bytes)
let kem_encap pk nonce =
  (KemEncap pk nonce, KemSecretShared nonce)

/// Destructor

[@@"opaque_to_smt"]
val kem_decap: bytes -> bytes -> option bytes
let kem_decap sk encap =
  match encap with
  | KemEncap (KemPub sk') nonce ->
    if sk = sk' then
      Some (KemSecretShared nonce)
    else
      None
  | _ -> None

/// Reduction rule

val kem_decap_encap:
  sk:bytes -> nonce:bytes ->
  Lemma (
    let (kem_output, ss) = kem_encap (kem_pk sk) nonce in
    kem_decap sk kem_output == Some ss
  )
let kem_decap_encap sk nonce =
  normalize_term_spec kem_encap;
  normalize_term_spec kem_decap;
  normalize_term_spec kem_pk

/// Lemma for attacker knowledge theorem.

val kem_pk_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable tr sk)
  (ensures is_publishable tr (kem_pk sk))
let kem_pk_preserves_publishability #ci tr sk =
  normalize_term_spec kem_pk;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// User lemma (kem_pk bytes invariant)

val bytes_invariant_kem_pk:
  {|crypto_invariants|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant tr sk)
  (ensures bytes_invariant tr (kem_pk sk))
  [SMTPat (bytes_invariant tr (kem_pk sk))]
let bytes_invariant_kem_pk #ci tr sk =
  normalize_term_spec bytes_invariant;
  normalize_term_spec kem_pk

/// User lemma (kem_pk sk label)

val get_label_kem_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures (
    get_label (kem_pk sk) == public
  ))
  [SMTPat (get_label (kem_pk sk))]
let get_label_kem_pk #cu sk =
  normalize_term_spec get_label;
  normalize_term_spec kem_pk

/// User lemma (kem_pk sk usage)

val get_kem_sk_usage_kem_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures (
    get_kem_sk_usage (kem_pk sk) == get_usage sk
  ))
  [SMTPat (get_kem_sk_usage (kem_pk sk))]
let get_kem_sk_usage_kem_pk #cu sk =
  normalize_term_spec get_kem_sk_usage;
  normalize_term_spec kem_pk

/// User lemma (kem_pk sk label)

val get_kem_sk_label_kem_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures (
    get_kem_sk_label (kem_pk sk) == get_label sk
  ))
  [SMTPat (get_kem_sk_label (kem_pk sk))]
let get_kem_sk_label_kem_pk #cu sk =
  normalize_term_spec get_kem_sk_label;
  normalize_term_spec kem_pk

/// Lemma for attacker knowledge theorem.

val kem_encap_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  pk:bytes -> nonce:bytes ->
  Lemma
  (requires
    is_publishable tr pk /\
    is_publishable tr nonce
  )
  (ensures (
    let (kem_output, ss) = kem_encap pk nonce in
    is_publishable tr kem_output /\
    is_publishable tr ss
  ))
let kem_encap_preserves_publishability #ci tr pk nonce =
  normalize_term_spec kem_encap;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  assert(is_publishable tr (KemSecretShared nonce))

/// Lemma for attacker knowledge theorem.

val kem_decap_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> encap:bytes ->
  Lemma
  (requires
    is_publishable tr sk /\
    is_publishable tr encap
  )
  (ensures (
    match kem_decap sk encap with
    | Some ss -> is_publishable tr ss
    | None -> True
  ))
let kem_decap_preserves_publishability #ci tr sk encap =
  normalize_term_spec kem_decap;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  normalize_term_spec get_kem_sk_label;
  match encap with
  | KemEncap (KemPub sk') nonce ->
    if sk = sk' then ()
    else ()
  | _ -> ()

/// User lemma (kem_encap properties)

val bytes_invariant_kem_encap:
  {|crypto_invariants|} -> tr:trace ->
  pk:bytes -> nonce:bytes ->
  Lemma
  (requires
    is_publishable tr pk /\
    bytes_invariant tr nonce /\
    KemNonce? (get_usage nonce) /\
    (get_label nonce) `can_flow tr` (get_kem_sk_label pk) /\ (
      get_label nonce `can_flow tr` public \/
      get_kem_sk_usage pk == KemKey (KemNonce?.usg (get_usage nonce))
    )
  )
  (ensures (
    let (kem_output, ss) = kem_encap pk nonce in
    is_publishable tr kem_output /\
    bytes_invariant tr ss /\
    get_label ss == get_label nonce /\
    get_usage ss == (KemNonce?.usg (get_usage nonce))
  ))
  [SMTPat (kem_encap pk nonce); SMTPat (bytes_invariant tr nonce)]
let bytes_invariant_kem_encap #ci tr pk nonce =
  normalize_term_spec kem_encap;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_usage;
  normalize_term_spec get_kem_sk_usage;
  normalize_term_spec get_label;
  normalize_term_spec get_kem_sk_label;
  let (kem_output, ss) = kem_encap pk nonce in
  ()

/// User lemma (kem_decap usage)

#push-options "--z3rlimit 25"
val get_usage_kem_decap:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> encap:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr encap /\
    (KemKey? (get_usage sk) \/ (get_label sk) `can_flow tr` public)
  )
  (ensures (
    match kem_decap sk encap with
    | Some ss -> get_usage sk == KemKey (get_usage ss) \/ get_label ss `can_flow tr` public
    | None -> True
  ))
  [SMTPat (kem_decap sk encap); SMTPat (bytes_invariant tr encap)]
let get_usage_kem_decap #ci tr sk encap =
  normalize_term_spec kem_decap;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_usage;
  normalize_term_spec get_kem_sk_usage;
  normalize_term_spec get_label;
  normalize_term_spec get_kem_sk_label;
  match encap with
  | KemEncap (KemPub sk') nonce ->
    if sk = sk' then ()
    else ()
  | _ -> ()
#pop-options

/// User lemma (kem_decap invariant)

#push-options "--z3rlimit 25"
val bytes_invariant_kem_decap:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> encap:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr encap
  )
  (ensures (
    match kem_decap sk encap with
    | Some ss -> is_knowable_by (get_label sk) tr ss
    | None -> True
  ))
  [SMTPat (kem_decap sk encap); SMTPat (bytes_invariant tr encap)]
let bytes_invariant_kem_decap #ci tr sk encap =
  normalize_term_spec kem_decap;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  normalize_term_spec get_kem_sk_label;
  match encap with
  | KemEncap (KemPub sk') nonce ->
    if sk = sk' then ()
    else ()
  | _ -> ()
#pop-options
