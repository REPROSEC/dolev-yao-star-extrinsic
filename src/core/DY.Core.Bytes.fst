module DY.Core.Bytes

open DY.Core.Bytes.Type
open DY.Core.Trace.Type
open DY.Core.Trace.Base
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
  | Rand len time ->
    len
  | Concat left right ->
    length left + length right
  | AeadEnc key nonce msg ad ->
    16 + length msg
  | Pk sk ->
    32
  | PkeEnc pk nonce msg ->
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

/// The well-formedness invariant preserved by any protocol using the DY* API,
/// whether it is proved secure or not.
/// It checks whether all `Rand`om bytes inside a given `bytes`
/// correspond to a `RandGen` entry in the trace.
/// This property is weaker than the full-fledged `bytes_invariant` (see theorem `bytes_invariant_implies_well_formed`).
/// It is a crucial precondition to ensure that the result of `get_label`
/// is independent of the trace (see theorem `get_label_later`).

[@@"opaque_to_smt"]
val bytes_well_formed: trace -> bytes -> prop
let rec bytes_well_formed tr b =
  match b with
  | Literal buf ->
    True
  | Rand len time ->
    time < trace_length tr /\
    RandGen? (get_entry_at tr time)
  | Concat left right ->
    bytes_well_formed tr left /\
    bytes_well_formed tr right
  | AeadEnc key nonce msg ad ->
    bytes_well_formed tr key /\
    bytes_well_formed tr nonce /\
    bytes_well_formed tr msg /\
    bytes_well_formed tr ad
  | Pk sk ->
    bytes_well_formed tr sk
  | PkeEnc pk nonce msg ->
    bytes_well_formed tr pk /\
    bytes_well_formed tr nonce /\
    bytes_well_formed tr msg
  | Vk sk ->
    bytes_well_formed tr sk
  | Sign sk nonce msg ->
    bytes_well_formed tr sk /\
    bytes_well_formed tr nonce /\
    bytes_well_formed tr msg
  | Hash msg ->
    bytes_well_formed tr msg
  | DhPub sk ->
    bytes_well_formed tr sk
  | Dh sk pk ->
    bytes_well_formed tr sk /\
    bytes_well_formed tr pk
  | KdfExtract salt ikm ->
    bytes_well_formed tr salt /\
    bytes_well_formed tr ikm
  | KdfExpand prk info len ->
    bytes_well_formed tr prk /\
    bytes_well_formed tr info
  | KemPub sk ->
    bytes_well_formed tr sk
  | KemEncap pk nonce ->
    bytes_well_formed tr pk /\
    bytes_well_formed tr nonce
  | KemSecretShared nonce ->
    bytes_well_formed tr nonce

val bytes_well_formed_later:
  tr1:trace -> tr2:trace ->
  b:bytes ->
  Lemma
  (requires
    bytes_well_formed tr1 b /\
    tr1 <$ tr2
  )
  (ensures bytes_well_formed tr2 b)
  [SMTPat (bytes_well_formed tr1 b);
   SMTPat (bytes_well_formed tr2 b);
   SMTPat (tr1 <$ tr2)]
let rec bytes_well_formed_later tr1 tr2 b =
  normalize_term_spec bytes_well_formed;
  introduce forall b_sub. (b_sub << b /\ bytes_well_formed tr1 b_sub) ==> bytes_well_formed tr2 b_sub with (
    introduce _ ==> _ with _. (
      bytes_well_formed_later tr1 tr2 b_sub
    )
  );
  match b with
  | Literal buf -> ()
  | Rand len time -> (
    assert(entry_at tr1 time (get_entry_at tr1 time))
  )
  | Concat left right -> ()
  | AeadEnc key nonce msg ad -> ()
  | Pk sk -> ()
  | PkeEnc pk nonce msg -> ()
  | Vk sk -> ()
  | Sign sk nonce msg -> ()
  | Hash msg -> ()
  | DhPub sk -> ()
  | Dh sk pk -> ()
  | KdfExtract salt ikm -> ()
  | KdfExpand prk info len -> ()
  | KemPub sk -> ()
  | KemEncap pk nonce -> ()
  | KemSecretShared nonce -> ()

/// Many lemmas with SMT patterns can help proving `bytes_well_formed`.
/// These lemmas are not expected to be useful in most situations:
/// - in general we have `bytes_invariant` that implies `bytes_well_formed`
///   (see theorem `bytes_invariant_implies_well_formed`),
/// - the only place where we cannot rely on `bytes_invariant`
///   are in the `pred_later` lemmas inside `crypto_predicates`,
///   which is only a small amount of the security proof.
/// Hence the SMT patterns do not trigger by default,
/// and can be enabled by doing `enable_bytes_well_formed_smtpats tr;`.
/// See https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns
/// for more information on this technique.

[@@"opaque_to_smt"]
let bytes_well_formed_smtpats_enabled (tr:trace) = True

val enable_bytes_well_formed_smtpats:
  tr:trace ->
  Lemma (bytes_well_formed_smtpats_enabled tr)
let enable_bytes_well_formed_smtpats tr =
  normalize_term_spec (bytes_well_formed_smtpats_enabled tr)

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

val default_kdf_expand_crypto_usage: kdf_expand_crypto_usage
let default_kdf_expand_crypto_usage = {
  get_usage = (fun prk_usage info -> NoUsage);
  get_label = (fun prk_usage prk_label info -> prk_label);
  get_label_lemma = (fun tr prk_usage prk_label info -> ());
}

val default_crypto_usages: crypto_usages
let default_crypto_usages = {
  dh_usage = default_dh_crypto_usage;
  kdf_expand_usage = default_kdf_expand_crypto_usage;
}

/// Obtain the usage of a given bytestring.
/// See DY.Core.Bytes.Type for more explanations.

#push-options "--ifuel 2"
[@@"opaque_to_smt"]
val get_usage: {|crypto_usages|} -> trace -> bytes -> usage
let rec get_usage #cusages tr b =
  match b with
  | Rand len time ->
    if time < trace_length tr then (
      match get_entry_at tr time with
      | RandGen usg _ _ -> usg
      | _ -> NoUsage // garbage
    ) else (
      NoUsage // garbage
    )
  | Dh sk1 (DhPub sk2) -> (
    match get_usage tr sk1, get_usage tr sk2 with
    | DhKey _ _, DhKey _ _ ->
      dh_usage.known_peer_usage (get_usage tr sk1) (get_usage tr sk2)
    | DhKey _ _, _ ->
      dh_usage.unknown_peer_usage (get_usage tr sk1)
    | _, DhKey _ _ ->
      dh_usage.unknown_peer_usage (get_usage tr sk2)
    | _, _ ->
      NoUsage
  )
  | Dh sk pk -> (
    match get_usage tr sk with
    | DhKey _ _ -> dh_usage.unknown_peer_usage (get_usage tr sk)
    | _ -> NoUsage
  )
  | KdfExtract salt ikm -> (
    KdfExpandKey "KDF.ExtractedKey" (Literal (Seq.empty))
  )
  | KdfExpand prk info len -> (
    let prk_usage = get_usage tr prk in
    if KdfExpandKey? prk_usage then
      kdf_expand_usage.get_usage prk_usage info
    else
      NoUsage
  )
  | KemSecretShared nonce -> (
    match get_usage tr nonce with
    | KemNonce usg -> usg
    | _ -> NoUsage
  )
  | _ -> NoUsage
#pop-options

val get_usage_later:
  {|crypto_usages|} ->
  tr1:trace -> tr2:trace ->
  b:bytes ->
  Lemma
  (requires
    bytes_well_formed tr1 b /\
    tr1 <$ tr2
  )
  (ensures get_usage tr1 b == get_usage tr2 b)
let rec get_usage_later #cusgs tr1 tr2 b =
  normalize_term_spec bytes_well_formed;
  normalize_term_spec get_usage;
  match b with
  | Rand len time ->
    assert(entry_at tr1 time (get_entry_at tr1 time))
  | Dh sk1 (DhPub sk2) ->
    get_usage_later tr1 tr2 sk1;
    get_usage_later tr1 tr2 sk2
  | Dh sk pk ->
    get_usage_later tr1 tr2 sk
  | KdfExtract salt ikm -> ()
  | KdfExpand prk info len ->
    get_usage_later tr1 tr2 prk
  | KemSecretShared nonce ->
    get_usage_later tr1 tr2 nonce
  | _ -> ()

/// Obtain the label of a given bytestring.

#push-options "--ifuel 2"
[@@"opaque_to_smt"]
val get_label: {|crypto_usages|} -> trace -> bytes -> label
let rec get_label #cusages tr b =
  match b with
  | Literal buf ->
    public
  | Rand len time ->
    if time < trace_length tr then (
      match get_entry_at tr time with
      | RandGen _ lab _ -> lab
      | _ -> DY.Core.Label.Unknown.unknown_label
    ) else (
      DY.Core.Label.Unknown.unknown_label
    )
  | Concat left right ->
    meet (get_label tr left) (get_label tr right)
  | AeadEnc key nonce msg ad ->
    public
  | Pk sk ->
    public
  | PkeEnc pk nonce msg ->
    public
  | Vk sk ->
    public
  | Sign sk nonce msg ->
    get_label tr msg
  | Hash msg ->
    get_label tr msg
  | DhPub sk ->
    public
  | Dh sk1 (DhPub sk2) ->
    join (get_label tr sk1) (get_label tr sk2)
  | Dh sk pk ->
    public
  | KdfExtract salt ikm ->
    meet (get_label tr salt) (get_label tr ikm)
  | KdfExpand prk info len -> (
    let prk_usage = get_usage tr prk in
    if KdfExpandKey? prk_usage then
      kdf_expand_usage.get_label prk_usage (get_label tr prk) info
    else
      get_label tr prk
  )
  | KemPub sk ->
    public
  | KemEncap pk nonce ->
    public
  | KemSecretShared nonce ->
    get_label tr nonce
#pop-options

val get_label_later:
  {|crypto_usages|} ->
  tr1:trace -> tr2:trace ->
  b:bytes ->
  Lemma
  (requires
    bytes_well_formed tr1 b /\
    tr1 <$ tr2
  )
  (ensures get_label tr1 b == get_label tr2 b)
  [SMTPat (get_label tr1 b); SMTPat (tr1 <$ tr2)]
let rec get_label_later #cusgs tr1 tr2 b =
  normalize_term_spec bytes_well_formed;
  normalize_term_spec get_label;
  match b with
  | Literal buf -> ()
  | Rand len time ->
    assert(entry_at tr1 time (get_entry_at tr1 time))
  | Concat left right ->
    get_label_later tr1 tr2 left;
    get_label_later tr1 tr2 right
  | AeadEnc key nonce msg ad -> ()
  | Pk sk -> ()
  | PkeEnc pk nonce msg -> ()
  | Vk sk -> ()
  | Sign sk nonce msg ->
    get_label_later tr1 tr2 msg
  | Hash msg ->
    get_label_later tr1 tr2 msg
  | DhPub sk -> ()
  | Dh sk1 (DhPub sk2) ->
    get_label_later tr1 tr2 sk1;
    get_label_later tr1 tr2 sk2
  | Dh sk pk -> ()
  | KdfExtract salt ikm ->
    get_label_later tr1 tr2 salt;
    get_label_later tr1 tr2 ikm
  | KdfExpand prk info len ->
    get_label_later tr1 tr2 prk;
    get_usage_later tr1 tr2 prk
  | KemPub sk -> ()
  | KemEncap pk nonce -> ()
  | KemSecretShared nonce ->
    get_label_later tr1 tr2 nonce

/// Is it safe to use a bytestring as if it had some given usage?
///
/// In real-world protocols, we are rarely 100% certain that a key has some usage.
/// Indeed, the usage information might come from verifying a signature,
/// but when the signature key is corrupt we might be wrong on the actual key usage.
///
/// The meaning of
///   key `has_usage tr` usg
/// is:
/// - either the usage of `key` is `usg`,
/// - or `key` is publishable.
/// In the second case, it is safe to use as a key with usage `usg`
/// because it would be as-if the computations were performed by the attacker.

[@@"opaque_to_smt"]
val has_usage:
  {|crypto_usages|} ->
  trace -> bytes -> usage ->
  prop
let has_usage #cusgs tr msg usg =
  get_usage tr msg == usg \/
  (get_label tr msg) `can_flow tr` public

val has_usage_later:
  {|crypto_usages|} ->
  tr1:trace -> tr2:trace ->
  msg:bytes -> usg:usage ->
  Lemma
  (requires
    msg `has_usage tr1` usg /\
    bytes_well_formed tr1 msg /\
    tr1 <$ tr2
  )
  (ensures msg `has_usage tr2` usg)
  [SMTPat (msg `has_usage tr1` usg); SMTPat (tr1 <$ tr2)]
let has_usage_later #cusgs tr1 tr2 msg usg =
  reveal_opaque (`%has_usage) has_usage;
  get_usage_later tr1 tr2 msg

val has_usage_inj:
  {|crypto_usages|} ->
  tr:trace -> msg:bytes ->
  usg1:usage -> usg2:usage ->
  Lemma
  (requires
    msg `has_usage tr` usg1 /\
    msg `has_usage tr` usg2
  )
  (ensures usg1 == usg2 \/ (get_label tr msg) `can_flow tr` public)
let has_usage_inj #cusgs tr msg usg1 usg2 =
  reveal_opaque (`%has_usage) has_usage

val has_usage_publishable:
  {|crypto_usages|} ->
  tr:trace -> msg:bytes -> usg:usage ->
  Lemma
  (requires (get_label tr msg) `can_flow tr` public)
  (ensures msg `has_usage tr` usg)
let has_usage_publishable #cusgs tr msg usg =
  reveal_opaque (`%has_usage) has_usage

/// Helper functions to lift `get_label` and `has_usage` to private keys corresponding to given public keys.
/// Although the public keys are public,
/// these functions are useful to reason on the corresponding private key.

[@@"opaque_to_smt"]
val extract_preserves_well_formedness:
  (bytes -> GTot (option bytes)) ->
  bytes -> 
  prop
let extract_preserves_well_formedness extract msg =
  forall tr.
    bytes_well_formed tr msg ==> (
      match extract msg with
      | None -> True
      | Some sk -> bytes_well_formed tr sk
    )

[@@"opaque_to_smt"]
val mk_get_xxx_label:
  {|crypto_usages|} ->
  (bytes -> GTot (option bytes)) ->
  trace -> bytes -> label
let mk_get_xxx_label #cusgs extract tr pk =
  match extract pk with
  | Some sk -> get_label tr sk
  | None -> public

val mk_get_xxx_label_later:
  {|crypto_usages|} ->
  extract:(bytes -> GTot (option bytes)) ->
  tr1:trace -> tr2:trace ->
  msg:bytes ->
  Lemma
  (requires
    bytes_well_formed tr1 msg /\
    tr1 <$ tr2 /\
    extract_preserves_well_formedness extract msg
  )
  (ensures mk_get_xxx_label extract tr1 msg == mk_get_xxx_label extract tr2 msg)
  [SMTPat (mk_get_xxx_label extract tr1 msg); SMTPat (tr1 <$ tr2)]
let mk_get_xxx_label_later #cusgs extract tr1 tr2 msg =
  reveal_opaque (`%mk_get_xxx_label) mk_get_xxx_label;
  reveal_opaque (`%extract_preserves_well_formedness) extract_preserves_well_formedness

[@@"opaque_to_smt"]
val mk_has_xxx_usage:
  {|crypto_usages|} ->
  (bytes -> GTot (option bytes)) ->
  trace -> bytes -> usage -> prop
let mk_has_xxx_usage #cusgs extract tr pk usg =
  match extract pk with
  | Some sk -> sk `has_usage tr` usg
  | None -> True

val mk_has_xxx_usage_later:
  {|crypto_usages|} ->
  extract:(bytes -> GTot (option bytes)) ->
  tr1:trace -> tr2:trace ->
  msg:bytes -> usg:usage ->
  Lemma
  (requires
    msg `mk_has_xxx_usage extract tr1` usg /\
    bytes_well_formed tr1 msg /\
    tr1 <$ tr2 /\
    extract_preserves_well_formedness extract msg
  )
  (ensures msg `mk_has_xxx_usage extract tr2` usg)
  [SMTPat (msg `mk_has_xxx_usage extract tr1` usg); SMTPat (tr1 <$ tr2)]
let mk_has_xxx_usage_later #cusgs extract tr1 tr2 msg usg =
  reveal_opaque (`%mk_has_xxx_usage) mk_has_xxx_usage;
  reveal_opaque (`%extract_preserves_well_formedness) extract_preserves_well_formedness

val mk_has_xxx_usage_inj:
  {|crypto_usages|} ->
  extract:(bytes -> GTot (option bytes)) ->
  tr:trace -> msg:bytes ->
  usg1:usage -> usg2:usage ->
  Lemma
  (requires
    msg `mk_has_xxx_usage extract tr` usg1 /\
    msg `mk_has_xxx_usage extract tr` usg2
  )
  (ensures usg1 == usg2 \/ (mk_get_xxx_label extract tr msg) `can_flow tr` public)
let mk_has_xxx_usage_inj #cusgs extract tr msg usg1 usg2 =
  reveal_opaque (`%mk_get_xxx_label) mk_get_xxx_label;
  reveal_opaque (`%mk_has_xxx_usage) mk_has_xxx_usage;
  match extract msg with
  | Some sk -> has_usage_inj tr sk usg1 usg2
  | None -> ()

val mk_has_xxx_usage_publishable:
  {|crypto_usages|} ->
  extract:(bytes -> GTot (option bytes)) ->
  tr:trace -> msg:bytes -> usg:usage ->
  Lemma
  (requires (mk_get_xxx_label extract tr msg) `can_flow tr` public)
  (ensures msg `mk_has_xxx_usage extract tr` usg)
let mk_has_xxx_usage_publishable #cusgs extract tr msg usg =
  reveal_opaque (`%mk_get_xxx_label) mk_get_xxx_label;
  reveal_opaque (`%mk_has_xxx_usage) mk_has_xxx_usage;
  match extract msg with
  | Some sk -> has_usage_publishable tr sk usg
  | None -> ()

/// Instantiation for public-key encryption

[@@"opaque_to_smt"]
val extract_sk: bytes -> GTot (option bytes)
let extract_sk pk =
  match pk with
  | Pk sk -> Some sk
  | _ -> None

val extract_sk_preserves_well_formedness:
  pk:bytes ->
  Lemma (extract_preserves_well_formedness extract_sk pk)
  [SMTPat (extract_preserves_well_formedness extract_sk pk)]
let extract_sk_preserves_well_formedness pk =
  normalize_term_spec bytes_well_formed;
  reveal_opaque (`%extract_sk) extract_sk;
  reveal_opaque (`%extract_preserves_well_formedness) extract_preserves_well_formedness

val get_sk_label: {|crypto_usages|} -> trace -> bytes -> label
let get_sk_label #cusgs = mk_get_xxx_label extract_sk

val has_sk_usage: {|crypto_usages|} -> trace -> bytes -> usage -> prop
let has_sk_usage #cusgs = mk_has_xxx_usage extract_sk

/// Instantiation for signatures

[@@"opaque_to_smt"]
val extract_signkey: bytes -> GTot (option bytes)
let extract_signkey vk =
  match vk with
  | Vk sk -> Some sk
  | _ -> None

val extract_signkey_preserves_well_formedness:
  pk:bytes ->
  Lemma (extract_preserves_well_formedness extract_signkey pk)
  [SMTPat (extract_preserves_well_formedness extract_signkey pk)]
let extract_signkey_preserves_well_formedness pk =
  normalize_term_spec bytes_well_formed;
  reveal_opaque (`%extract_signkey) extract_signkey;
  reveal_opaque (`%extract_preserves_well_formedness) extract_preserves_well_formedness

val get_signkey_label: {|crypto_usages|} -> trace -> bytes -> label
let get_signkey_label #cusgs = mk_get_xxx_label extract_signkey

val has_signkey_usage: {|crypto_usages|} -> trace -> bytes -> usage -> prop
let has_signkey_usage #cusgs = mk_has_xxx_usage extract_signkey

/// Instantiation for Diffie-Hellman

[@@"opaque_to_smt"]
val extract_dh_sk: bytes -> GTot (option bytes)
let extract_dh_sk pk =
  match pk with
  | DhPub sk -> Some sk
  | _ -> None

val extract_dh_sk_preserves_well_formedness:
  pk:bytes ->
  Lemma (extract_preserves_well_formedness extract_dh_sk pk)
  [SMTPat (extract_preserves_well_formedness extract_dh_sk pk)]
let extract_dh_sk_preserves_well_formedness pk =
  normalize_term_spec bytes_well_formed;
  reveal_opaque (`%extract_dh_sk) extract_dh_sk;
  reveal_opaque (`%extract_preserves_well_formedness) extract_preserves_well_formedness

val get_dh_label: {|crypto_usages|} -> trace -> bytes -> label
let get_dh_label #cusgs = mk_get_xxx_label extract_dh_sk

val has_dh_usage: {|crypto_usages|} -> trace -> bytes -> usage -> prop
let has_dh_usage #cusgs = mk_has_xxx_usage extract_dh_sk

/// Instantiation for KEM

[@@"opaque_to_smt"]
val extract_kem_sk: bytes -> GTot (option bytes)
let extract_kem_sk pk =
  match pk with
  | KemPub sk -> Some sk
  | _ -> None

val extract_kem_sk_preserves_well_formedness:
  pk:bytes ->
  Lemma (extract_preserves_well_formedness extract_kem_sk pk)
  [SMTPat (extract_preserves_well_formedness extract_kem_sk pk)]
let extract_kem_sk_preserves_well_formedness pk =
  normalize_term_spec bytes_well_formed;
  reveal_opaque (`%extract_kem_sk) extract_kem_sk;
  reveal_opaque (`%extract_preserves_well_formedness) extract_preserves_well_formedness

val get_kem_sk_label: {|crypto_usages|} -> trace -> bytes -> label
let get_kem_sk_label #cusgs = mk_get_xxx_label extract_kem_sk

val has_kem_sk_usage: {|crypto_usages|} -> trace -> bytes -> usage -> prop
let has_kem_sk_usage #cusgs = mk_has_xxx_usage extract_kem_sk

/// Customizable predicates stating how cryptographic functions may be used
/// by honest principals.

noeq
type aead_crypto_predicate {|crypto_usages|} = {
  pred: tr:trace -> key_usage:usage{AeadKey? key_usage} -> key:bytes{key `has_usage tr` key_usage} -> nonce:bytes -> msg:bytes -> ad:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    key_usage:usage{AeadKey? key_usage} -> key:bytes{key `has_usage tr1` key_usage} -> nonce:bytes -> msg:bytes -> ad:bytes ->
    Lemma
    (requires
      pred tr1 key_usage key nonce msg ad /\
      bytes_well_formed tr1 key /\
      bytes_well_formed tr1 nonce /\
      bytes_well_formed tr1 msg /\
      bytes_well_formed tr1 ad /\
      tr1 <$ tr2
    )
    (ensures pred tr2 key_usage key nonce msg ad)
  ;
}

noeq
type pke_crypto_predicate {|crypto_usages|} = {
  pred: tr:trace -> sk_usage:usage{PkeKey? sk_usage} -> pk:bytes{pk `has_sk_usage tr` sk_usage} -> msg:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    sk_usage:usage{PkeKey? sk_usage} -> pk:bytes -> msg:bytes ->
    Lemma
    (requires
      pk `has_sk_usage tr1` sk_usage /\
      pred tr1 sk_usage pk msg /\
      bytes_well_formed tr1 pk /\
      bytes_well_formed tr1 msg /\
      tr1 <$ tr2
    )
    (ensures pred tr2 sk_usage pk msg)
  ;
}

noeq
type sign_crypto_predicate {|crypto_usages|} = {
  pred: tr:trace -> sk_usage:usage{SigKey? sk_usage} -> vk:bytes{vk `has_signkey_usage tr` sk_usage} -> msg:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    sk_usage:usage{SigKey? sk_usage} -> vk:bytes -> msg:bytes ->
    Lemma
    (requires
      vk `has_signkey_usage tr1` sk_usage /\
      pred tr1 sk_usage vk msg /\
      bytes_well_formed tr1 vk /\
      bytes_well_formed tr1 msg /\
      tr1 <$ tr2
    )
    (ensures pred tr2 sk_usage vk msg)
  ;
}

noeq
type crypto_predicates {|crypto_usages|} = {
  aead_pred: aead_crypto_predicate;
  pke_pred: pke_crypto_predicate;
  sign_pred: sign_crypto_predicate;
}

/// Default (empty) cryptographic predicates, that can be used like this:
/// { default_crypto_predicates with
///   sign_pred = ...;
/// }

val default_aead_predicate: {|crypto_usages|} -> aead_crypto_predicate
let default_aead_predicate #cusages = {
  pred = (fun tr key_usage key nonce msg ad -> False);
  pred_later = (fun tr1 tr2 key_usage key nonce msg ad -> ());
}

val default_pke_predicate: {|crypto_usages|} -> pke_crypto_predicate
let default_pke_predicate #cusages = {
  pred = (fun tr sk_usage pk msg -> False);
  pred_later = (fun tr1 tr2 sk_usage pk msg -> ());
}

val default_sign_predicate: {|crypto_usages|} -> sign_crypto_predicate
let default_sign_predicate #cusages = {
  pred = (fun tr sk_usage sk msg -> False);
  pred_later = (fun tr1 tr2 sk_usage sk msg -> ());
}

val default_crypto_predicates:
  {|crypto_usages|} ->
  crypto_predicates
let default_crypto_predicates #cusages = {
  aead_pred = default_aead_predicate;
  pke_pred = default_pke_predicate;
  sign_pred = default_sign_predicate;
}

/// Gather the usage functions and the cryptographic predicates
/// to obtain the cryptographic invariants,
/// which will be a parameter of the bytes invariant.

class crypto_invariants = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  usages: crypto_usages;
  [@@@FStar.Tactics.Typeclasses.no_method]
  preds: crypto_predicates;
}

// `crypto_predicates` cannot be a typeclass that is inherited by `crypto_invariants`,
// hence we simulate inheritance like this.

let aead_pred {|cinvs:crypto_invariants|} = cinvs.preds.aead_pred
let pke_pred {|cinvs:crypto_invariants|} = cinvs.preds.pke_pred
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
  | Rand len time ->
    // Random bytes correspond to an entry
    (exists usage lab. entry_at tr time (RandGen usage lab len))
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
    (get_label tr nonce) `can_flow tr` public /\
    // the standard IND-CCA assumption do not guarantee indistinguishability of additional data,
    // hence it must flow to public
    (get_label tr ad) `can_flow tr` public /\
    (
      (
        exists key_usg.
        // Honest case:
        // - the key has the usage of AEAD key
        key `has_usage tr` key_usg /\
        AeadKey? key_usg /\
        // - the custom (protocol-specific) invariant hold (authentication)
        aead_pred.pred tr key_usg key nonce msg ad /\
        // - the message is less secret than the key
        //   (this is crucial so that decryption preserve publishability)
        (get_label tr msg) `can_flow tr` (get_label tr key)
      ) \/ (
        // Attacker case:
        // the key and message are both public
        (get_label tr key) `can_flow tr` public /\
        (get_label tr msg) `can_flow tr` public
      )
    )
  | Pk sk ->
    bytes_invariant tr sk
  | PkeEnc pk nonce msg ->
    bytes_invariant tr pk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    (
      (
        exists sk_usg.
        // Honest case:
        // - the key has the usage of asymetric encryption key
        pk `has_sk_usage tr` sk_usg /\
        PkeKey? sk_usg /\
        // - the custom (protocol-specific) invariant hold (authentication)
        pke_pred.pred tr sk_usg pk msg /\
        // - the message is less secret than the decryption key
        //   (this is crucial so that decryption preserve publishability)
        (get_label tr msg) `can_flow tr` (get_sk_label tr pk) /\
        // - the message is less secret than the nonce
        //   (this is because the standard IND-CCA security assumption
        //   do not give guarantees on the indistinguishability of the message
        //   when the attacker knows the nonce)
        (get_label tr msg) `can_flow tr` (get_label tr nonce) /\
        // - the nonce has the correct usage (for the same reason as above)
        nonce `has_usage tr` PkeNonce
      ) \/ (
        // Attacker case:
        // the attacker knows the message
        (get_label tr msg) `can_flow tr` public
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
        exists sk_usg.
        // Honest case:
        // - the key has the usage of signature key
        (Vk sk) `has_signkey_usage tr` sk_usg /\
        SigKey? sk_usg /\
        // - the custom (protocol-specific) invariant hold (authentication)
        sign_pred.pred tr sk_usg (Vk sk) msg /\
        // - the nonce is more secret than the signature key
        //   (this is because the standard EUF-CMA security assumption on signatures
        //   do not have any guarantees when the nonce is leaked to the attacker,
        //   in practice knowing the nonce used to sign a message
        //   can be used to obtain the private key,
        //   hence this restriction)
        (get_label tr sk) `can_flow tr` (get_label tr nonce) /\
        // - the nonce has the correct usage (for the same reason as above)
        nonce `has_usage tr` SigNonce
      ) \/ (
        // Attacker case:
        // the attacker knows the signature key.
        // The message is not required to be known by the attacker:
        // the EUF-CMA security assumption on signatures doesn't guarantee
        // that in case of signature forgeries.
        (get_label tr sk) `can_flow tr` public
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
        (exists sk1_usg. sk1 `has_usage tr` sk1_usg /\ DhKey? sk1_usg) \/
        (exists sk2_usg. sk2 `has_usage tr` sk2_usg /\ DhKey? sk2_usg)
      ) \/ (
        // Attacker case:
        // the attacker knows one of the secret keys
        (get_label tr sk1) `can_flow tr` public \/
        (get_label tr sk2) `can_flow tr` public
      )
    )
  | Dh sk pk ->
    bytes_invariant tr pk /\
    bytes_invariant tr sk /\
    (get_label tr pk) `can_flow tr` public /\
    (
      (
        exists sk_usg. sk `has_usage tr` sk_usg /\ DhKey? sk_usg
      ) \/ (
        (get_label tr sk) `can_flow tr` public
      )
    )
  | KdfExtract salt ikm ->
    bytes_invariant tr salt /\
    bytes_invariant tr ikm
  | KdfExpand prk info len ->
    bytes_invariant tr prk /\
    bytes_invariant tr info /\
    (
      (
        exists prk_usg.
        // Honest case:
        // the prk has correct usage
        prk `has_usage tr` prk_usg /\
        KdfExpandKey? prk_usg
      ) \/ (
        // Attacker case:
        // the attacker knows both prk and info
        (get_label tr prk) `can_flow tr` public
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
        (get_label tr nonce) `can_flow tr` (get_kem_sk_label tr pk) /\ (
        // nonce and pk agree on the usage of the shared secret
        // (this is because this KEM model does not bind the public key to the shared secret)
          exists ss_usg.
          pk `has_kem_sk_usage tr` (KemKey ss_usg) /\
          nonce `has_usage tr` (KemNonce ss_usg)
        )
      ) \/ (
        // Attacker case:
        // the attacker knows the nonce
        (get_label tr nonce) `can_flow tr` public
      )
    )
  | KemSecretShared nonce ->
    bytes_invariant tr nonce

val bytes_invariant_implies_well_formed:
  {|crypto_invariants|} ->
  tr:trace -> msg:bytes ->
  Lemma
  (requires bytes_invariant tr msg)
  (ensures bytes_well_formed tr msg)
  [SMTPat (bytes_well_formed tr msg);
   SMTPat (bytes_invariant tr msg)]
let rec bytes_invariant_implies_well_formed #cinvs tr b =
  normalize_term_spec bytes_invariant;
  normalize_term_spec bytes_well_formed;
  introduce forall b_sub. (b_sub << b /\ bytes_invariant tr b_sub) ==> bytes_well_formed tr b_sub with (
    introduce _ ==> _ with _. (
      bytes_invariant_implies_well_formed tr b_sub
    )
  )

/// The bytes invariant is preserved as the trace grows.

#push-options "--ifuel 2"
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
  | Rand len time -> ()
  | Concat left right ->
    bytes_invariant_later tr1 tr2 left;
    bytes_invariant_later tr1 tr2 right
  | AeadEnc key nonce msg ad -> (
    bytes_invariant_later tr1 tr2 key;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    bytes_invariant_later tr1 tr2 ad;
    introduce forall key_usg. key `has_usage tr1` key_usg /\ aead_pred.pred tr1 key_usg key nonce msg ad ==> aead_pred.pred tr2 key_usg key nonce msg ad with (
      introduce key `has_usage tr1` key_usg /\ aead_pred.pred tr1 key_usg key nonce msg ad ==> aead_pred.pred tr2 key_usg key nonce msg ad with _. (
        aead_pred.pred_later tr1 tr2 key_usg key nonce msg ad
      )
    )
  )
  | Pk sk ->
    bytes_invariant_later tr1 tr2 sk
  | PkeEnc pk nonce msg -> (
    bytes_invariant_later tr1 tr2 pk;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    introduce forall sk_usg. pk `has_sk_usage tr1` sk_usg /\ pke_pred.pred tr1 sk_usg pk msg ==> pke_pred.pred tr2 sk_usg pk msg with (
      introduce pk `has_sk_usage tr1` sk_usg /\ pke_pred.pred tr1 sk_usg pk msg ==> pke_pred.pred tr2 sk_usg pk msg with _. (
        pke_pred.pred_later tr1 tr2 sk_usg pk msg
      )
    )
  )
  | Vk sk ->
    bytes_invariant_later tr1 tr2 sk
  | Sign sk nonce msg -> (
    bytes_invariant_later tr1 tr2 sk;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    assert(bytes_invariant tr1 (Vk sk)); // to prove well-formedness
    introduce forall sk_usg. (Vk sk) `has_signkey_usage tr1` sk_usg /\ sign_pred.pred tr1 sk_usg (Vk sk) msg ==> sign_pred.pred tr2 sk_usg (Vk sk) msg with (
      introduce (Vk sk) `has_signkey_usage tr1` sk_usg /\ sign_pred.pred tr1 sk_usg (Vk sk) msg ==> sign_pred.pred tr2 sk_usg (Vk sk) msg with _. (
        sign_pred.pred_later tr1 tr2 sk_usg (Vk sk) msg
      )
    )
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
#pop-options

(*** Various predicates ***)

/// Below are a few shorthand predicates on bytes,
/// that are derived from bytes invariant, label and usage.
/// They capture common properties we use to reason on bytestrings.
/// They are not opaque to SMT because users have to reason with their definitions.

/// Is a given bytestring less secret than a given label?
/// In other words, can the bytestring be known to principals captured by this label?

val is_knowable_by: {|crypto_invariants|} -> label -> trace -> bytes -> prop
let is_knowable_by #cinvs lab tr b =
  bytes_invariant tr b /\ (get_label tr b) `can_flow tr` lab

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
  bytes_invariant tr b /\ (get_label tr b) == lab

/// Shorthand predicates for the various type of keys.

val is_verification_key: {|crypto_invariants|} -> usg:usage{SigKey? usg} -> label -> trace -> bytes -> prop
let is_verification_key #cinvs usg lab tr b =
  is_publishable tr b /\ (get_signkey_label tr b) == lab /\
  b `has_signkey_usage tr` usg

val is_signature_key: {|crypto_invariants|} -> usg:usage{SigKey? usg} -> label -> trace -> bytes -> prop
let is_signature_key #cinvs usg lab tr b =
  is_secret lab tr b /\
  b `has_usage tr` usg

val is_encryption_key: {|crypto_invariants|} -> usg:usage{PkeKey? usg} -> label -> trace -> bytes -> prop
let is_encryption_key #cinvs usg lab tr b =
  is_publishable tr b /\ (get_sk_label tr b) == lab /\
  b `has_sk_usage tr` usg

val is_decryption_key: {|crypto_invariants|} -> usg:usage{PkeKey? usg} -> label -> trace -> bytes -> prop
let is_decryption_key #cinvs usg lab tr b =
  is_secret lab tr b /\
  b `has_usage tr` usg

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

/// User lemma (well-formedness)

val bytes_well_formed_literal_to_bytes:
  tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma (bytes_well_formed tr (literal_to_bytes lit))
  [SMTPat (bytes_well_formed tr (literal_to_bytes lit));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_literal_to_bytes tr lit =
  normalize_term_spec bytes_well_formed;
  normalize_term_spec literal_to_bytes

/// User lemma (bytes invariant).

val bytes_invariant_literal_to_bytes:
  {|crypto_invariants|} -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (ensures bytes_invariant tr (literal_to_bytes lit))
  [SMTPat (bytes_invariant tr (literal_to_bytes lit))]
let bytes_invariant_literal_to_bytes #cinvs tr lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_invariant

val get_label_literal_to_bytes:
  {|crypto_usages|} -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (ensures get_label tr (literal_to_bytes lit) == public)
  [SMTPat (get_label tr (literal_to_bytes lit))]
let get_label_literal_to_bytes #cusgs tr lit =
  normalize_term_spec literal_to_bytes;
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

/// User lemma (concatenation well-formedness)

val bytes_well_formed_concat:
  tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (bytes_well_formed tr (concat b1 b2) == (bytes_well_formed tr b1 /\ bytes_well_formed tr b2))
  [SMTPat (bytes_well_formed tr (concat b1 b2));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_concat tr b1 b2 =
  normalize_term_spec concat;
  normalize_term_spec bytes_well_formed

/// User lemma (splitting well-formedness)

val bytes_well_formed_split:
  tr:trace ->
  b:bytes -> i:nat ->
  Lemma (
    match split b i with
    | None -> True
    | Some (b1, b2) -> bytes_well_formed tr b == (bytes_well_formed tr b1 /\ bytes_well_formed tr b2)
  )
  [SMTPat (bytes_well_formed tr b);
   SMTPat (split b i);
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_split tr b i =
  normalize_term_spec split;
  normalize_term_spec bytes_well_formed

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
  tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (ensures get_label tr (concat b1 b2) == meet (get_label tr b1) (get_label tr b2))
  [SMTPat (get_label tr (concat b1 b2))]
let get_label_concat tr b1 b2 =
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

/// User lemma (AEAD encryption well-formedness)

val bytes_well_formed_aead_enc:
  tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma (
    bytes_well_formed tr (aead_enc key nonce msg ad) == (
      bytes_well_formed tr key /\
      bytes_well_formed tr nonce /\
      bytes_well_formed tr msg /\
      bytes_well_formed tr ad
    )
  )
  [SMTPat (bytes_well_formed tr (aead_enc key nonce msg ad));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_aead_enc tr key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec bytes_well_formed

/// User lemma (AEAD decryption well-formedness)

val bytes_well_formed_aead_dec:
  tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (
    match aead_dec key nonce msg ad with
    | None -> True
    | Some plaintext -> (
      bytes_well_formed tr msg == (
        bytes_well_formed tr key /\
        bytes_well_formed tr nonce /\
        bytes_well_formed tr plaintext /\
        bytes_well_formed tr ad
      )
    )
  )
  [SMTPat (aead_dec key nonce msg ad);
   SMTPat (bytes_well_formed tr msg);
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_aead_dec tr key nonce msg ad =
  normalize_term_spec aead_dec;
  normalize_term_spec bytes_well_formed;
  match aead_dec key nonce msg ad with
  | None -> ()
  | Some msg -> ()

/// User lemma (AEAD encryption bytes invariant).

val bytes_invariant_aead_enc:
  {|crypto_invariants|} -> tr:trace ->
  key:bytes -> key_usg:usage -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    bytes_invariant tr key /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    bytes_invariant tr ad /\
    (get_label tr nonce) `can_flow tr` public /\
    (get_label tr ad) `can_flow tr` public /\
    (get_label tr msg) `can_flow tr` (get_label tr key) /\
    key `has_usage tr` key_usg /\
    (
      (
        AeadKey? key_usg /\
        aead_pred.pred tr key_usg key nonce msg ad
      ) \/ (
        get_label tr key `can_flow tr` public
      )
    )
  )
  (ensures bytes_invariant tr (aead_enc key nonce msg ad))
  [SMTPat (bytes_invariant tr (aead_enc key nonce msg ad));
   SMTPat (key `has_usage tr` key_usg)]
let bytes_invariant_aead_enc #cinvs tr key key_usg nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec bytes_invariant

/// User lemma (AEAD encryption label).

val get_label_aead_enc:
  {|crypto_usages|} ->
  tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (ensures get_label tr (aead_enc key nonce msg ad) == public)
  [SMTPat (get_label tr (aead_enc key nonce msg ad))]
let get_label_aead_enc #cusages tr key nonce msg ad =
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
      is_knowable_by (get_label tr key) tr plaintext /\
      (
        (
          forall key_usg.
          key `has_usage tr` key_usg /\
          AeadKey? key_usg ==>
          aead_pred.pred tr key_usg key nonce plaintext ad
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
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (has_usage_inj tr key));
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
val pke_enc: bytes -> bytes -> bytes -> bytes
let pke_enc pk nonce msg =
  PkeEnc pk nonce msg

/// Destructor.

[@@"opaque_to_smt"]
val pke_dec: bytes -> bytes -> option bytes
let pke_dec sk msg =
  match msg with
  | PkeEnc (Pk sk') nonce res ->
    if sk = sk' then
      Some res
    else
      None
  | _ -> None

/// Symbolic reduction rule.

val pke_dec_enc:
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (pke_dec sk (pke_enc (pk sk) nonce msg) == Some msg)
let pke_dec_enc key nonce msg =
  normalize_term_spec pke_dec;
  normalize_term_spec pke_enc;
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

val pke_enc_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable tr pk /\
    is_publishable tr nonce /\
    is_publishable tr msg
  )
  (ensures is_publishable tr (pke_enc pk nonce msg))
let pke_enc_preserves_publishability #cinvs tr pk nonce msg =
  normalize_term_spec pke_enc;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

/// Lemma for attacker knowledge theorem.

#push-options "--z3rlimit 25"
val pke_dec_preserves_publishability:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable tr sk /\
    is_publishable tr msg
  )
  (ensures (
    match pke_dec sk msg with
    | Some res -> is_publishable tr res
    | None -> True
  ))
let pke_dec_preserves_publishability #cinvs tr sk msg =
  normalize_term_spec pke_dec;
  normalize_term_spec get_sk_label;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label
#pop-options

/// User lemma (public encryption key well-formedness)

val bytes_well_formed_pk:
  tr:trace ->
  sk:bytes ->
  Lemma
  (bytes_well_formed tr (pk sk) == bytes_well_formed tr sk)
  [SMTPat (bytes_well_formed tr (pk sk));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_pk tr sk =
  normalize_term_spec pk;
  normalize_term_spec bytes_well_formed

/// User lemma (public-key encryption well-formedness)

val bytes_well_formed_pke_enc:
  tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma (
    bytes_well_formed tr (pke_enc pk nonce msg) == (
      bytes_well_formed tr pk /\
      bytes_well_formed tr nonce /\
      bytes_well_formed tr msg
    )
  )
  [SMTPat (bytes_well_formed tr (pke_enc pk nonce msg));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_pke_enc tr pk nonce msg =
  normalize_term_spec pke_enc;
  normalize_term_spec bytes_well_formed

/// User lemma (public-key decryption well-formedness)

val bytes_well_formed_pke_dec:
  tr:trace ->
  sk:bytes -> msg:bytes ->
  Lemma
  (ensures (
    match pke_dec sk msg with
    | None -> True
    | Some plaintext ->
      bytes_well_formed tr msg ==> (
        bytes_well_formed tr sk /\
        bytes_well_formed tr plaintext
        // would have equality if we could add `bytes_well_formed tr nonce`
        // (unfortunately we don't have the nonce)
      )
  ))
  [SMTPat (pke_dec sk msg);
   SMTPat (bytes_well_formed tr msg);
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_pke_dec tr sk msg =
  normalize_term_spec pke_dec;
  normalize_term_spec pk;
  normalize_term_spec bytes_well_formed


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
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures get_label tr (pk sk) == public)
  [SMTPat (get_label tr (pk sk))]
let get_label_pk #cusages tr sk =
  normalize_term_spec pk;
  normalize_term_spec get_label

/// User lemma (public encryption key sk label).

val get_sk_label_pk:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures get_sk_label tr (pk sk) == get_label tr sk)
  [SMTPat (get_sk_label tr (pk sk))]
let get_sk_label_pk #cusages tr sk =
  normalize_term_spec pk;
  normalize_term_spec get_sk_label

/// User lemma (public encryption key sk usage).

val has_sk_usage_pk:
  {|crypto_usages|} ->
  tr:trace -> sk:bytes -> usg:usage ->
  Lemma
  (ensures (pk sk) `has_sk_usage tr` usg == sk `has_usage tr` usg)
  [SMTPat ((pk sk) `has_sk_usage tr` usg)]
let has_sk_usage_pk #cusages tr sk usg =
  normalize_term_spec pk;
  normalize_term_spec mk_has_xxx_usage;
  normalize_term_spec extract_sk

/// User lemma (public-key encryption bytes invariant).

val bytes_invariant_pke_enc:
  {|crypto_invariants|} -> tr:trace ->
  pk:bytes -> sk_usg:usage -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant tr pk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    (get_label tr msg) `can_flow tr` (get_sk_label tr pk) /\
    (get_label tr msg) `can_flow tr` (get_label tr nonce) /\
    pk `has_sk_usage tr` sk_usg /\
    nonce `has_usage tr` PkeNonce /\
    (
      (
        PkeKey? sk_usg /\
        pke_pred.pred tr sk_usg pk msg
      ) \/ (
        (get_label tr msg) `can_flow tr` public
      )
    )
  )
  (ensures bytes_invariant tr (pke_enc pk nonce msg))
  [SMTPat (bytes_invariant tr (pke_enc pk nonce msg));
   SMTPat (pk `has_sk_usage tr` sk_usg)]
let bytes_invariant_pke_enc #cinvs tr pk pke_usg nonce msg =
  normalize_term_spec pke_enc;
  normalize_term_spec bytes_invariant

/// User lemma (public-key encryption label).

val get_label_pke_enc:
  {|crypto_usages|} ->
  tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label tr (pke_enc pk nonce msg) == public)
  [SMTPat (get_label tr (pke_enc pk nonce msg))]
let get_label_pke_enc #cusages tr pk nonce msg =
  normalize_term_spec pke_enc;
  normalize_term_spec get_label

/// User lemma (public-key decryption bytes invariant).

#push-options "--z3rlimit 25"
val bytes_invariant_pke_dec:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> sk_usg:usage -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr msg /\
    sk `has_usage tr` sk_usg
  )
  (ensures (
    match pke_dec sk msg with
    | None -> True
    | Some plaintext ->
      is_knowable_by (get_label tr sk) tr plaintext /\
      (
        (
          PkeKey? sk_usg /\
          pke_pred.pred tr sk_usg (pk sk) plaintext
        ) \/ (
          (get_label tr plaintext) `can_flow tr` public
        )
      )
  ))
  [SMTPat (pke_dec sk msg);
   SMTPat (bytes_invariant tr msg);
   SMTPat (sk `has_usage tr` sk_usg)
  ]
let bytes_invariant_pke_dec #cinvs tr sk sk_usg msg =
  normalize_term_spec pke_dec;
  normalize_term_spec pk;
  normalize_term_spec get_sk_label;
  normalize_term_spec get_label;
  normalize_term_spec bytes_invariant;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (has_usage_inj tr sk));
  assert(forall sk_usg. sk `has_usage tr` sk_usg == (pk sk) `has_sk_usage tr` sk_usg)
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

/// User lemma (verification key well-formedness)

val bytes_well_formed_vk:
  tr:trace ->
  sk:bytes ->
  Lemma (bytes_well_formed tr (vk sk) == bytes_well_formed tr sk)
  [SMTPat (bytes_well_formed tr (vk sk));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_vk tr sk =
  normalize_term_spec vk;
  normalize_term_spec bytes_well_formed

/// User lemma (signature bytes well-formedness)

val bytes_well_formed_sign:
  tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma (
    bytes_well_formed tr (sign sk nonce msg) == (
      bytes_well_formed tr sk /\
      bytes_well_formed tr nonce /\
      bytes_well_formed tr msg
    )
  )
  [SMTPat (bytes_well_formed tr (sign sk nonce msg));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_sign tr sk nonce msg =
  normalize_term_spec sign;
  normalize_term_spec vk;
  normalize_term_spec bytes_well_formed

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
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures get_label tr (vk sk) == public)
  [SMTPat (get_label tr (vk sk))]
let get_label_vk #cusages tr sk =
  normalize_term_spec vk;
  normalize_term_spec get_label

/// User lemma (verification key signkey label).

val get_signkey_label_vk:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures get_signkey_label tr (vk sk) == get_label tr sk)
  [SMTPat (get_signkey_label tr (vk sk))]
let get_signkey_label_vk #cusages tr sk =
  normalize_term_spec vk;
  normalize_term_spec get_signkey_label

/// User lemma (verification key signkey usage).

val has_signkey_usage_vk:
  {|crypto_usages|} ->
  tr:trace -> sk:bytes -> usg:usage ->
  Lemma
  (ensures (vk sk) `has_signkey_usage tr` usg == sk `has_usage tr` usg)
  [SMTPat ((vk sk) `has_signkey_usage tr` usg)]
let has_signkey_usage_vk #cusages tr sk usg =
  normalize_term_spec vk;
  normalize_term_spec mk_has_xxx_usage;
  normalize_term_spec extract_signkey

/// User lemma (signature bytes invariant).

val bytes_invariant_sign:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> sk_usg:usage -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    sk `has_usage tr` sk_usg /\
    nonce `has_usage tr` SigNonce /\
    (get_label tr sk) `can_flow tr` (get_label tr nonce) /\
    (
      (
        SigKey? sk_usg /\
        sign_pred.pred tr sk_usg (vk sk) msg
      ) \/ (
        get_label tr sk `can_flow tr` public
      )
    )
  )
  (ensures bytes_invariant tr (sign sk nonce msg))
  [SMTPat (bytes_invariant tr (sign sk nonce msg));
   SMTPat (sk `has_usage tr` sk_usg)]
let bytes_invariant_sign #cinvs tr sk sk_usg nonce msg =
  normalize_term_spec sign;
  normalize_term_spec vk;
  normalize_term_spec bytes_invariant

/// User lemma (signature label).

val get_label_sign:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label tr (sign sk nonce msg) == get_label tr msg)
  [SMTPat (get_label tr (sign sk nonce msg))]
let get_label_sign #cusages tr sk nonce msg =
  normalize_term_spec sign;
  normalize_term_spec get_label

/// User lemma (verification bytes invariant).

val bytes_invariant_verify:
  {|crypto_invariants|} -> tr:trace ->
  vk:bytes -> sk_usg:usage -> msg:bytes -> signature:bytes ->
  Lemma
  (requires
    bytes_invariant tr vk /\
    bytes_invariant tr msg /\
    bytes_invariant tr signature /\
    vk `has_signkey_usage tr` sk_usg /\
    verify vk msg signature
  )
  (ensures
    (
      SigKey? sk_usg ==>
      sign_pred.pred tr sk_usg vk msg
    ) \/ (
      (get_signkey_label tr vk) `can_flow tr` public
    )
  )
  [SMTPat (verify vk msg signature);
   SMTPat (bytes_invariant tr signature);
   SMTPat (vk `has_signkey_usage tr` sk_usg)
  ]
let bytes_invariant_verify #cinvs tr vkey sk_usg msg signature =
  normalize_term_spec verify;
  normalize_term_spec get_signkey_label;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  normalize_term_spec vk;
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 (has_usage_inj tr));
  assert(forall sk. Vk sk == vk sk)

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

/// User lemma (hash bytes well-formedness)

val bytes_well_formed_hash:
  tr:trace ->
  msg:bytes ->
  Lemma (bytes_well_formed tr (hash msg) == bytes_well_formed tr msg)
  [SMTPat (bytes_well_formed tr (hash msg));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_hash tr msg =
  normalize_term_spec hash;
  normalize_term_spec bytes_well_formed

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
  tr:trace ->
  msg:bytes ->
  Lemma (get_label tr (hash msg) == get_label tr msg)
  [SMTPat (get_label tr (hash msg))]
let get_label_hash #cusages tr msg =
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

#push-options "--z3rlimit 25"
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
#pop-options

/// User lemma (dh_pk well-formedness)

val bytes_well_formed_dh_pk:
  tr:trace ->
  sk:bytes ->
  Lemma (bytes_well_formed tr (dh_pk sk) == bytes_well_formed tr sk)
  [SMTPat (bytes_well_formed tr (dh_pk sk));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_dh_pk tr sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  normalize_term_spec bytes_well_formed

/// User lemma (dh well-formedness)

val bytes_well_formed_dh:
  tr:trace ->
  sk:bytes -> pk:bytes ->
  Lemma (bytes_well_formed tr (dh sk pk) <==> (bytes_well_formed tr sk /\ bytes_well_formed tr pk))
  [SMTPat (bytes_well_formed tr (dh sk pk));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_dh tr sk pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec bytes_well_formed

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
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures get_label tr (dh_pk sk) == public)
  [SMTPat (get_label tr (dh_pk sk))]
let get_label_dh_pk tr sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  normalize_term_spec get_label

/// User lemma (get_dh_label on DH public key ).

val get_dh_label_dh_pk:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (get_dh_label tr (dh_pk sk) == get_label tr sk)
  [SMTPat (get_dh_label tr (dh_pk sk))]
let get_dh_label_dh_pk tr sk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%mk_get_xxx_label) (mk_get_xxx_label);
  reveal_opaque (`%extract_dh_sk) (extract_dh_sk)

/// User lemma (get_dh_usage on DH public key ).

val has_dh_usage_dh_pk:
  {|crypto_usages|} ->
  tr:trace -> sk:bytes -> usg:usage ->
  Lemma
  ((dh_pk sk) `has_dh_usage tr` usg == sk `has_usage tr` usg)
  [SMTPat ((dh_pk sk) `has_dh_usage tr` usg)]
let has_dh_usage_dh_pk tr sk usg =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%mk_has_xxx_usage) (mk_has_xxx_usage);
  reveal_opaque (`%extract_dh_sk) (extract_dh_sk)

/// User lemma (dh bytes invariant)

val bytes_invariant_dh:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> sk_usg:usage -> pk:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    sk `has_usage tr` sk_usg /\
    DhKey? sk_usg /\
    is_publishable tr pk
  )
  (ensures bytes_invariant tr (dh sk pk))
  [SMTPat (bytes_invariant tr (dh sk pk));
   SMTPat (sk `has_usage tr` sk_usg)]
let bytes_invariant_dh tr sk sk_usg pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec bytes_invariant

/// User lemma (dh bytes label)

val get_label_dh:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes -> pk:bytes ->
  Lemma
  (ensures (get_label tr (dh sk pk)) == ((get_label tr sk) `join` (get_dh_label tr pk)))
  [SMTPat (get_label tr (dh sk pk))]
let get_label_dh tr sk pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec get_dh_label;
  normalize_term_spec get_label;
  join_commutes (get_label tr sk) (get_dh_label tr pk)

/// User lemma (dh bytes usage with known peer)

val has_usage_dh_known_peer:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes -> sk_usg:usage -> pk:bytes -> pk_usg:usage ->
  Lemma
  (requires
    sk `has_usage tr` sk_usg /\
    DhKey? sk_usg /\
    pk `has_dh_usage tr` pk_usg /\
    DhKey? pk_usg
  )
  (ensures (
    (dh sk pk) `has_usage tr` (dh_usage.known_peer_usage sk_usg pk_usg)
  ))
  [SMTPat (has_usage tr (dh sk pk));
   SMTPat (sk `has_usage tr` sk_usg);
   SMTPat (pk `has_dh_usage tr` pk_usg);
  ]
let has_usage_dh_known_peer tr sk sk_usg pk pk_usg =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec has_dh_usage;
  normalize_term_spec get_usage;
  reveal_opaque (`%has_usage) (has_usage);
  normalize_term_spec get_label;
  dh_usage.known_peer_usage_commutes sk_usg pk_usg;
  FStar.Classical.move_requires (has_usage_publishable tr (dh sk pk)) (dh_usage.known_peer_usage sk_usg pk_usg)

/// User lemma (dh bytes usage with unknown peer)

val has_usage_dh_unknown_peer:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes -> sk_usg:usage -> pk:bytes ->
  Lemma
  (requires
    sk `has_usage tr` sk_usg /\
    DhKey? sk_usg /\
    dh_usage.unknown_peer_usage sk_usg <> NoUsage
  )
  (ensures (
    (dh sk pk) `has_usage tr` (dh_usage.unknown_peer_usage sk_usg)
  ))
  [SMTPat (has_usage tr (dh sk pk));
   SMTPat (sk `has_usage tr` sk_usg)]
let has_usage_dh_unknown_peer tr sk sk_usg pk =
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%dh) (dh);
  normalize_term_spec get_usage;
  reveal_opaque (`%has_usage) (has_usage);
  FStar.Classical.forall_intro (FStar.Classical.move_requires (dh_usage.unknown_peer_usage_implies sk_usg));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (dh_usage.known_peer_usage_commutes sk_usg))

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
  normalize_term_spec get_label

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
  let prk_usage = get_usage tr prk in
  if KdfExpandKey? prk_usage then
    kdf_expand_usage.get_label_lemma tr prk_usage (get_label tr prk) info
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

/// User lemma (kdf_extract well-formedness)

val bytes_well_formed_kdf_extract:
  tr:trace ->
  salt:bytes -> ikm:bytes ->
  Lemma (
    bytes_well_formed tr (kdf_extract salt ikm) == (
      bytes_well_formed tr salt /\
      bytes_well_formed tr ikm
    )
  )
  [SMTPat (bytes_well_formed tr (kdf_extract salt ikm));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_kdf_extract tr salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  normalize_term_spec bytes_well_formed

/// User lemma (kdf_expand well-formedness)

val bytes_well_formed_kdf_expand:
  tr:trace ->
  prk:bytes -> info:bytes -> len:nat{len <> 0} ->
  Lemma (
    bytes_well_formed tr (kdf_expand prk info len) == (
      bytes_well_formed tr prk /\
      bytes_well_formed tr info
    )
  )
  [SMTPat (bytes_well_formed tr (kdf_expand prk info len));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_kdf_expand tr prk info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec bytes_well_formed

/// User lemma (kdf_extract preserves bytes invariant)

val bytes_invariant_kdf_extract:
  {|crypto_invariants|} ->
  tr:trace ->
  salt:bytes -> ikm:bytes ->
  Lemma
  (requires
    bytes_invariant tr salt /\
    bytes_invariant tr ikm
  )
  (ensures bytes_invariant tr (kdf_extract salt ikm))
  [SMTPat (bytes_invariant tr (kdf_extract salt ikm))]
let bytes_invariant_kdf_extract tr salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  normalize_term_spec bytes_invariant

/// User lemma (kdf_extract usage)

val has_usage_kdf_extract:
  {|crypto_usages|} ->
  tr:trace ->
  salt:bytes -> ikm:bytes ->
  Lemma
  (ensures (
    (kdf_extract salt ikm) `has_usage tr` (KdfExpandKey "KDF.ExtractedKey" (literal_to_bytes Seq.empty))
  ))
  [SMTPat (has_usage tr (kdf_extract salt ikm))]
let has_usage_kdf_extract tr salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  reveal_opaque (`%has_usage) (has_usage);
  reveal_opaque (`%literal_to_bytes) (literal_to_bytes);
  normalize_term_spec get_usage

/// User lemma (kdf_extract label)

val get_label_kdf_extract:
  {|crypto_usages|} ->
  tr:trace ->
  salt:bytes -> ikm:bytes ->
  Lemma
  (ensures (
    get_label tr (kdf_extract salt ikm) == (get_label tr salt) `meet` (get_label tr ikm)
  ))
  [SMTPat (get_label tr (kdf_extract salt ikm))]
let get_label_kdf_extract tr salt ikm =
  reveal_opaque (`%kdf_extract) (kdf_extract);
  normalize_term_spec get_label

/// User lemma (kdf_expand preserves bytes invariant)

val bytes_invariant_kdf_expand:
  {|crypto_invariants|} ->
  tr:trace ->
  prk:bytes -> prk_usage:usage -> info:bytes -> len:nat{len <> 0} ->
  Lemma
  (requires
    bytes_invariant tr prk /\
    bytes_invariant tr info /\
    prk `has_usage tr` prk_usage /\
    KdfExpandKey? prk_usage
  )
  (ensures bytes_invariant tr (kdf_expand prk info len))
  [SMTPat (bytes_invariant tr (kdf_expand prk info len));
   SMTPat (prk `has_usage tr` prk_usage)]
let bytes_invariant_kdf_expand tr prk prk_usage info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  reveal_opaque (`%has_usage) (has_usage);
  normalize_term_spec bytes_invariant

/// User lemma (kdf_expand usage)

val has_usage_kdf_expand:
  {|crypto_usages|} ->
  tr:trace ->
  prk:bytes -> prk_usage:usage -> info:bytes -> len:nat{len <> 0} ->
  Lemma
  (requires
    prk `has_usage tr` prk_usage /\
    KdfExpandKey? prk_usage
  )
  (ensures (
    (kdf_expand prk info len) `has_usage tr` (kdf_expand_usage.get_usage prk_usage info)
  ))
  [SMTPat (has_usage tr (kdf_expand prk info len));
   SMTPat (prk `has_usage tr` prk_usage)]
let has_usage_kdf_expand tr prk prk_usage info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  reveal_opaque (`%has_usage) (has_usage);
  normalize_term_spec get_usage;
  normalize_term_spec get_label;
  if KdfExpandKey? (get_usage tr prk) then
    kdf_expand_usage.get_label_lemma tr (get_usage tr prk) (get_label tr prk) info
  else ()

/// User lemma (kdf_expand label)

val get_label_kdf_expand:
  {|crypto_usages|} ->
  tr:trace ->
  prk:bytes -> prk_usage:usage -> info:bytes -> len:nat{len <> 0} ->
  Lemma
  (requires
    prk `has_usage tr` prk_usage /\
    KdfExpandKey? prk_usage
  )
  (ensures (
    get_label tr (kdf_expand prk info len) `equivalent tr` kdf_expand_usage.get_label prk_usage (get_label tr prk) info
  ))
  [SMTPat (get_label tr (kdf_expand prk info len));
   SMTPat (prk `has_usage tr` prk_usage)]
let get_label_kdf_expand tr prk prk_usage info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  reveal_opaque (`%has_usage) (has_usage);
  kdf_expand_usage.get_label_lemma tr prk_usage (get_label tr prk) info;
  normalize_term_spec get_label;
  if KdfExpandKey? (get_usage tr prk) then
    kdf_expand_usage.get_label_lemma tr (get_usage tr prk) (get_label tr prk) info
  else ()

/// User lemma (kdf_expand label can flow)

val get_label_kdf_expand_can_flow:
  {|crypto_usages|} ->
  tr:trace ->
  prk:bytes -> info:bytes -> len:nat{len <> 0} ->
  Lemma (get_label tr (kdf_expand prk info len) `can_flow tr` (get_label tr prk))
  [SMTPat (can_flow tr (get_label tr (kdf_expand prk info len)))]
let get_label_kdf_expand_can_flow tr prk info len =
  reveal_opaque (`%kdf_expand) (kdf_expand);
  normalize_term_spec get_label;
  match get_usage tr prk with
  | KdfExpandKey _ _ ->
    kdf_expand_usage.get_label_lemma tr (get_usage tr prk) (get_label tr prk) info
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
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures (
    get_label tr (kem_pk sk) == public
  ))
  [SMTPat (get_label tr (kem_pk sk))]
let get_label_kem_pk #cu tr sk =
  normalize_term_spec get_label;
  normalize_term_spec kem_pk

/// User lemma (kem_pk sk usage)

val has_kem_sk_usage_kem_pk:
  {|crypto_usages|} ->
  tr:trace -> sk:bytes -> usg:usage ->
  Lemma
  (ensures (
    has_kem_sk_usage tr (kem_pk sk) usg == has_usage tr sk usg
  ))
  [SMTPat (has_kem_sk_usage tr (kem_pk sk) usg)]
let has_kem_sk_usage_kem_pk #cu tr sk usg =
  normalize_term_spec kem_pk;
  normalize_term_spec mk_has_xxx_usage;
  normalize_term_spec extract_kem_sk

/// User lemma (kem_pk sk label)

val get_kem_sk_label_kem_pk:
  {|crypto_usages|} ->
  tr:trace ->
  sk:bytes ->
  Lemma
  (ensures (
    get_kem_sk_label tr (kem_pk sk) == get_label tr sk
  ))
  [SMTPat (get_kem_sk_label tr (kem_pk sk))]
let get_kem_sk_label_kem_pk #cu tr sk =
  normalize_term_spec get_kem_sk_label;
  normalize_term_spec kem_pk

/// Lemma for attacker knowledge theorem.

#push-options "--z3rlimit 25"
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
#pop-options

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
    if sk = sk' then (
      assert(get_label tr (KemSecretShared nonce) `can_flow tr` public)
    )
    else ()
  | _ -> ()

/// User lemma (kem_pk well-formedness)

val bytes_well_formed_kem_pk:
  tr:trace ->
  sk:bytes ->
  Lemma (bytes_well_formed tr (kem_pk sk) == bytes_well_formed tr sk)
  [SMTPat (bytes_well_formed tr (kem_pk sk));
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_kem_pk tr sk =
  normalize_term_spec bytes_well_formed;
  normalize_term_spec kem_pk

/// User lemma (kem_encap well-formedness)

val bytes_well_formed_kem_encap:
  tr:trace ->
  pk:bytes -> nonce:bytes ->
  Lemma
  (ensures (
    let (kem_output, ss) = kem_encap pk nonce in
    bytes_well_formed tr kem_output == (
      bytes_well_formed tr pk /\
      bytes_well_formed tr nonce
    ) /\
    bytes_well_formed tr ss == bytes_well_formed tr nonce
  ))
  [SMTPat (kem_encap pk nonce);
   SMTPat (bytes_well_formed tr nonce);
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_kem_encap tr pk nonce =
  normalize_term_spec kem_encap;
  normalize_term_spec bytes_well_formed;
  let (kem_output, ss) = kem_encap pk nonce in
  ()

/// User lemma (kem_decap well-formedness)

val bytes_well_formed_kem_decap:
  tr:trace ->
  sk:bytes -> encap:bytes ->
  Lemma
  (ensures (
    match kem_decap sk encap with
    | Some ss -> bytes_well_formed tr encap == (bytes_well_formed tr sk /\ bytes_well_formed tr ss)
    | None -> True
  ))
  [SMTPat (kem_decap sk encap);
   SMTPat (bytes_well_formed tr encap);
   SMTPat (bytes_well_formed_smtpats_enabled tr)]
let bytes_well_formed_kem_decap tr sk encap =
  normalize_term_spec kem_decap;
  normalize_term_spec bytes_well_formed;
  match encap with
  | KemEncap (KemPub sk') nonce ->
    if sk = sk' then ()
    else ()
  | _ -> ()

/// User lemma (kem_encap properties)

val bytes_invariant_kem_encap:
  {|crypto_invariants|} -> tr:trace ->
  pk:bytes -> nonce:bytes -> usg:usage ->
  Lemma
  (requires
    bytes_invariant tr pk /\
    bytes_invariant tr nonce /\
    nonce `has_usage tr` KemNonce usg /\
    (
      (
        pk `has_kem_sk_usage tr` KemKey usg /\
        (get_label tr nonce) `can_flow tr` (get_kem_sk_label tr pk)
      ) \/ (
        (get_label tr nonce) `can_flow tr` public
      )
    )
  )
  (ensures (
    let (kem_output, ss) = kem_encap pk nonce in
    is_publishable tr kem_output /\
    bytes_invariant tr ss /\
    get_label tr ss == get_label tr nonce /\
    ss `has_usage tr` usg
  ))
  [SMTPat (kem_encap pk nonce);
   SMTPat (nonce `has_usage tr` KemNonce usg)
  ]
let bytes_invariant_kem_encap #ci tr pk nonce usg =
  normalize_term_spec kem_encap;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label;
  normalize_term_spec get_usage;
  reveal_opaque (`%has_kem_sk_usage) (has_kem_sk_usage);
  reveal_opaque (`%has_usage) (has_usage);
  normalize_term_spec get_label;
  normalize_term_spec get_kem_sk_label;
  let (kem_output, ss) = kem_encap pk nonce in
  ()

/// User lemma (kem_decap usage)

#push-options "--z3rlimit 25"
val has_usage_kem_decap:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> sk_usg:usage -> encap:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr encap /\
    sk `has_usage tr` sk_usg /\
    KemKey? sk_usg
  )
  (ensures (
    match kem_decap sk encap with
    | Some ss -> ss `has_usage tr` (KemKey?.usg sk_usg)
    | None -> True
  ))
  [SMTPat (kem_decap sk encap); SMTPat (sk `has_usage tr` sk_usg)]
let has_usage_kem_decap #ci tr sk sk_usg encap =
  normalize_term_spec kem_decap;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_usage;
  reveal_opaque (`%has_usage) (has_usage);
  normalize_term_spec has_kem_sk_usage;
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
    | Some ss -> is_knowable_by (get_label tr sk) tr ss
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
