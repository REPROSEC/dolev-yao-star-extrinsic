module DY.Core.Bytes

open DY.Core.Bytes.Type
open DY.Core.Trace.Type
open DY.Core.Label.Type
open DY.Core.Label

#set-options "--fuel 1 --ifuel 1"

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
  | Aead key nonce msg ad ->
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

class crypto_usages = {
   [@@@FStar.Tactics.Typeclasses.no_method]
  __nothing: unit;
}

val default_crypto_usages: crypto_usages
let default_crypto_usages = {
  __nothing = ();
}

[@@"opaque_to_smt"]
val get_usage: {|crypto_usages|} -> bytes -> GTot usage
let get_usage #cusages b =
  match b with
  | Rand usg label len time ->
    usg
  | _ -> Unknown

[@@"opaque_to_smt"]
val get_label: {|crypto_usages|} -> bytes -> GTot label
let rec get_label #cusages b =
  match b with
  | Literal buf ->
    public
  | Rand usg label len time ->
    label
  | Concat left right ->
    meet (get_label left) (get_label right)
  | Aead key nonce msg ad ->
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

[@@"opaque_to_smt"]
val get_sk_label: {|crypto_usages|} -> bytes -> GTot label
let get_sk_label #cusages pk =
  match pk with
  | Pk sk -> get_label sk
  | _ -> public

[@@"opaque_to_smt"]
val get_sk_usage: {|crypto_usages|} -> bytes -> GTot usage
let get_sk_usage #cusages pk =
  match pk with
  | Pk sk -> get_usage sk
  | _ -> Unknown

[@@"opaque_to_smt"]
val get_signkey_label: {|crypto_usages|} -> bytes -> GTot label
let get_signkey_label #cusages pk =
  match pk with
  | Vk sk -> get_label sk
  | _ -> public

[@@"opaque_to_smt"]
val get_signkey_usage: {|crypto_usages|} -> bytes -> GTot usage
let get_signkey_usage #cusages pk =
  match pk with
  | Vk sk -> get_usage sk
  | _ -> Unknown

noeq
type crypto_predicates (cusages:crypto_usages) = {
  aead_pred: tr:trace -> key:bytes{AeadKey? (get_usage key)} -> nonce:bytes -> msg:bytes -> ad:bytes -> prop;
  aead_pred_later:
    tr1:trace -> tr2:trace ->
    key:bytes{AeadKey? (get_usage key)} -> nonce:bytes -> msg:bytes -> ad:bytes ->
    Lemma
    (requires aead_pred tr1 key nonce msg ad /\ tr1 <$ tr2)
    (ensures aead_pred tr2 key nonce msg ad)
  ;

  pkenc_pred: tr:trace -> pk:bytes{PkdecKey? (get_sk_usage pk)} -> msg:bytes -> prop;
  pkenc_pred_later:
    tr1:trace -> tr2:trace ->
    pk:bytes{PkdecKey? (get_sk_usage pk)} -> msg:bytes ->
    Lemma
    (requires pkenc_pred tr1 pk msg /\ tr1 <$ tr2)
    (ensures pkenc_pred tr2 pk msg)
  ;

  sign_pred: tr:trace -> vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes -> prop;
  sign_pred_later:
    tr1:trace -> tr2:trace ->
    vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes ->
    Lemma
    (requires sign_pred tr1 vk msg /\ tr1 <$ tr2)
    (ensures sign_pred tr2 vk msg)
  ;

  // ...
}

val default_crypto_predicates:
  cusages:crypto_usages ->
  crypto_predicates cusages
let default_crypto_predicates cusages = {
  aead_pred = (fun tr key nonce msg ad -> False);
  aead_pred_later = (fun tr1 tr2 key nonce msg ad -> ());

  pkenc_pred = (fun tr pk msg -> False);
  pkenc_pred_later = (fun tr1 tr2 pk msg -> ());

  sign_pred = (fun tr vk msg -> False);
  sign_pred_later = (fun tr1 tr2 vk msg -> ());
}

class crypto_invariants = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  usages: crypto_usages;
  [@@@FStar.Tactics.Typeclasses.no_method]
  preds: crypto_predicates usages;
}

let aead_pred {|cinvs:crypto_invariants|} = cinvs.preds.aead_pred
let aead_pred_later {|cinvs:crypto_invariants|} = cinvs.preds.aead_pred_later
let pkenc_pred {|cinvs:crypto_invariants|} = cinvs.preds.pkenc_pred
let pkenc_pred_later {|cinvs:crypto_invariants|} = cinvs.preds.pkenc_pred_later
let sign_pred {|cinvs:crypto_invariants|} = cinvs.preds.sign_pred
let sign_pred_later {|cinvs:crypto_invariants|} = cinvs.preds.sign_pred_later

[@@"opaque_to_smt"]
val bytes_invariant: {|crypto_invariants|} -> trace -> bytes -> prop
let rec bytes_invariant #cinvs tr b =
  match b with
  | Literal buf ->
    True
  | Rand usage label len time ->
    event_at tr time (RandGen usage label len)
  | Concat left right ->
    bytes_invariant tr left /\
    bytes_invariant tr right
  | Aead key nonce msg ad ->
    bytes_invariant tr key /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    bytes_invariant tr ad /\
    (get_label nonce) `can_flow tr` public /\
    (get_label ad) `can_flow tr` public /\
    (
      (
        // Honest case
        AeadKey? (get_usage key) /\
        cinvs.preds.aead_pred tr key nonce msg ad /\
        (get_label msg) `can_flow tr` (get_label key)
      ) \/ (
        // Attacker case
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
        // Honest case
        PkdecKey? (get_sk_usage pk) /\
        (get_label msg) `can_flow tr` (get_sk_label pk) /\
        (get_label msg) `can_flow tr` (get_label nonce) /\
        cinvs.preds.pkenc_pred tr pk msg
      ) \/ (
        // Attacker case
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
        // Honest case
        SigKey? (get_signkey_usage (Vk sk)) /\
        cinvs.preds.sign_pred tr (Vk sk) msg
      ) \/ (
        // Attacker case
        (get_label sk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Hash msg ->
    bytes_invariant tr msg

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
  | Aead key nonce msg ad -> (
    bytes_invariant_later tr1 tr2 key;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    bytes_invariant_later tr1 tr2 ad;
    match get_usage key with
    | AeadKey _ -> FStar.Classical.move_requires (cinvs.preds.aead_pred_later tr1 tr2 key nonce msg) ad
    | _ -> ()
  )
  | Pk sk ->
    bytes_invariant_later tr1 tr2 sk
  | PkEnc pk nonce msg -> (
    bytes_invariant_later tr1 tr2 pk;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    match get_sk_usage pk with
    | PkdecKey _ -> FStar.Classical.move_requires (cinvs.preds.pkenc_pred_later tr1 tr2 pk) msg
    | _ -> ()
  )
  | Vk sk ->
    bytes_invariant_later tr1 tr2 sk
  | Sign sk nonce msg -> (
    bytes_invariant_later tr1 tr2 sk;
    bytes_invariant_later tr1 tr2 nonce;
    bytes_invariant_later tr1 tr2 msg;
    match get_signkey_usage (Vk sk) with
    | SigKey _ -> FStar.Classical.move_requires (cinvs.preds.sign_pred_later tr1 tr2 (Vk sk)) msg
    | _ -> ()
  )
  | Hash msg ->
    bytes_invariant_later tr1 tr2 msg

(*** Various predicates ***)

val is_knowable_by: {|crypto_invariants|} -> label -> trace -> bytes -> prop
let is_knowable_by #cinvs lab tr b =
  bytes_invariant tr b /\ (get_label b) `can_flow tr` lab

val is_publishable: {|crypto_invariants|} -> trace -> bytes -> prop
let is_publishable #cinvs tr b =
  is_knowable_by public tr b

val is_secret: {|crypto_invariants|} -> label -> trace -> bytes -> prop
let is_secret #cinvs lab tr b =
  bytes_invariant tr b /\ (get_label b) == lab

val is_verification_key: {|crypto_invariants|} -> string -> label -> trace -> bytes -> prop
let is_verification_key #cinvs usg lab tr b =
  is_publishable tr b /\ (get_signkey_label b) == lab /\
  get_signkey_usage b == SigKey usg

val is_signature_key: {|crypto_invariants|} -> string -> label -> trace -> bytes -> prop
let is_signature_key #cinvs usg lab tr b =
  is_secret lab tr b /\
  get_usage b == SigKey usg

val is_encryption_key: {|crypto_invariants|} -> string -> label -> trace -> bytes -> prop
let is_encryption_key #cinvs usg lab tr b =
  is_publishable tr b /\ (get_sk_label b) == lab /\
  get_sk_usage b == PkdecKey usg

val is_decryption_key: {|crypto_invariants|} -> string -> label -> trace -> bytes -> prop
let is_decryption_key #cinvs usg lab tr b =
  is_secret lab tr b /\
  get_usage b == PkdecKey usg

(*** Literal ***)

[@@"opaque_to_smt"]
val literal_to_bytes: FStar.Seq.seq FStar.UInt8.t -> bytes
let literal_to_bytes lit =
  Literal lit

[@@"opaque_to_smt"]
val bytes_to_literal: bytes -> option (FStar.Seq.seq FStar.UInt8.t)
let bytes_to_literal msg =
  match msg with
  | Literal lit -> Some lit
  | _ -> None

// Symbolic reduction rule
val literal_to_bytes_to_literal:
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (bytes_to_literal (literal_to_bytes lit) == Some lit)
let literal_to_bytes_to_literal lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_to_literal

// Lemma for attacker knowledge theorem
val literal_to_bytes_is_publishable:
  {|crypto_invariants|} -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (is_publishable tr (literal_to_bytes lit))
let literal_to_bytes_is_publishable #cinvs tr lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_invariant;
  normalize_term_spec get_label

// Lemma for the user
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

val length_literal_to_bytes:
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma (length (literal_to_bytes lit) == FStar.Seq.length lit)
  [SMTPat (length (literal_to_bytes lit))]
let length_literal_to_bytes lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec length

val bytes_invariant_literal_to_bytes:
  {|crypto_invariants|} -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (ensures bytes_invariant tr (literal_to_bytes lit))
  [SMTPat (bytes_invariant tr (literal_to_bytes lit))]
let bytes_invariant_literal_to_bytes #cinvs tr lit =
  normalize_term_spec literal_to_bytes;
  normalize_term_spec bytes_invariant

(*** Concatenation ***)

[@@"opaque_to_smt"]
val concat: bytes -> bytes -> bytes
let concat left right =
  Concat left right

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

// Symbolic reduction rule
val split_concat:
  left:bytes -> right:bytes ->
  Lemma
  (split (concat left right) (length left) == Some (left, right))
let split_concat left right =
  normalize_term_spec split;
  normalize_term_spec concat

// Lemma for attacker knowledge theorem
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

// Lemma for attacker knowledge theorem
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

// Lemma for the user
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

val concat_length:
  left:bytes -> right:bytes ->
  Lemma
  (length (concat left right) = length left + length right)
let concat_length left right =
  normalize_term_spec concat;
  normalize_term_spec length

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

val get_label_concat:
  {|crypto_usages|} ->
  b1:bytes -> b2:bytes ->
  Lemma
  (ensures get_label (concat b1 b2) == meet (get_label b1) (get_label b2))
  [SMTPat (get_label (concat b1 b2))]
let get_label_concat b1 b2 =
  normalize_term_spec concat;
  normalize_term_spec get_label

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

[@@"opaque_to_smt"]
val aead_enc: bytes -> bytes -> bytes -> bytes -> bytes
let aead_enc key nonce msg ad =
  Aead key nonce msg ad

[@@"opaque_to_smt"]
val aead_dec: bytes -> bytes -> bytes -> bytes -> option bytes
let aead_dec key nonce msg ad =
  match msg with
  | Aead key' nonce' res ad' ->
    if key = key' && nonce = nonce' && ad = ad' then
      Some res
    else
      None
  | _ -> None

// Symbolic reduction rule
val aead_dec_enc:
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (aead_dec key nonce (aead_enc key nonce msg ad) ad == Some msg)
let aead_dec_enc key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec aead_dec

// Lemma for attacker knowledge theorem
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

// Lemma for attacker knowledge theorem
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
  // F* needs the match for some reason?
  match aead_dec key nonce msg ad with
  | Some res -> ()
  | None -> ()

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
    AeadKey? (get_usage key) /\
    aead_pred tr key nonce msg ad
  )
  (ensures bytes_invariant tr (aead_enc key nonce msg ad))
  [SMTPat (bytes_invariant tr (aead_enc key nonce msg ad))]
let bytes_invariant_aead_enc #cinvs tr key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec bytes_invariant

val get_label_aead_enc:
  {|crypto_usages|} ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (ensures get_label (aead_enc key nonce msg ad) = public)
  [SMTPat (get_label (aead_enc key nonce msg ad))]
let get_label_aead_enc #cusages key nonce msg ad =
  normalize_term_spec aead_enc;
  normalize_term_spec get_label

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
          aead_pred tr key nonce plaintext ad
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

[@@"opaque_to_smt"]
val pk: bytes -> bytes
let pk sk = Pk sk

[@@"opaque_to_smt"]
val pk_enc: bytes -> bytes -> bytes -> bytes
let pk_enc pk nonce msg =
  PkEnc pk nonce msg

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

// Symbolic reduction rule
val pk_dec_enc:
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (pk_dec sk (pk_enc (pk sk) nonce msg) == Some msg)
let pk_dec_enc key nonce msg =
  normalize_term_spec pk_dec;
  normalize_term_spec pk_enc;
  normalize_term_spec pk

// Lemma for attacker knowledge theorem
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

// Lemma for attacker knowledge theorem
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

// Lemma for attacker knowledge theorem
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

val get_label_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_label (pk sk) == public)
  [SMTPat (get_label (pk sk))]
let get_label_pk #cusages sk =
  normalize_term_spec pk;
  normalize_term_spec get_label

val get_sk_label_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_sk_label (pk sk) == get_label sk)
  [SMTPat (get_sk_label (pk sk))]
let get_sk_label_pk #cusages sk =
  normalize_term_spec pk;
  normalize_term_spec get_sk_label

val get_sk_usage_pk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_sk_usage (pk sk) == get_usage sk)
  [SMTPat (get_sk_usage (pk sk))]
let get_sk_usage_pk #cusages sk =
  normalize_term_spec pk;
  normalize_term_spec get_sk_usage

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
    PkdecKey? (get_sk_usage pk) /\
    pkenc_pred tr pk msg
  )
  (ensures bytes_invariant tr (pk_enc pk nonce msg))
  [SMTPat (bytes_invariant tr (pk_enc pk nonce msg))]
let bytes_invariant_pk_enc #cinvs tr pk nonce msg =
  normalize_term_spec pk_enc;
  normalize_term_spec bytes_invariant

val get_label_pk_enc:
  {|crypto_usages|} ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label (pk_enc pk nonce msg) == public)
  [SMTPat (get_label (pk_enc pk nonce msg))]
let get_label_pk_enc #cusages pk nonce msg =
  normalize_term_spec pk_enc;
  normalize_term_spec get_label

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
          PkdecKey? (get_sk_usage (pk sk)) ==>
          pkenc_pred tr (pk sk) plaintext
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

(*** Signature ***)

[@@"opaque_to_smt"]
val vk: bytes -> bytes
let vk sk = Vk sk

[@@"opaque_to_smt"]
val sign: bytes -> bytes -> bytes -> bytes
let sign sk nonce msg =
  Sign sk nonce msg

[@@"opaque_to_smt"]
val verify: bytes -> bytes -> bytes -> bool
let verify vk msg signature =
  match signature with
  | Sign sk nonce msg' ->
    vk = Vk sk && msg = msg'
  | _ -> false

// Symbolic reduction rule
val verify_sign:
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (verify (vk sk) msg (sign sk nonce msg))
let verify_sign sk nonce msg =
  normalize_term_spec vk;
  normalize_term_spec verify;
  normalize_term_spec sign

// Lemma for attacker knowledge theorem
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

// Lemma for attacker knowledge theorem
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

val bytes_invariant_vk:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant tr sk)
  (ensures bytes_invariant tr (pk sk))
  [SMTPat (bytes_invariant tr (pk sk))]
let bytes_invariant_vk #cinvs tr sk =
  normalize_term_spec vk;
  normalize_term_spec bytes_invariant

val get_label_vk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_label (vk sk) == public)
  [SMTPat (get_label (vk sk))]
let get_label_vk #cusages sk =
  normalize_term_spec vk;
  normalize_term_spec get_label

val get_signkey_label_vk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_signkey_label (vk sk) == get_label sk)
  [SMTPat (get_signkey_label (vk sk))]
let get_signkey_label_vk #cusages sk =
  normalize_term_spec vk;
  normalize_term_spec get_signkey_label

val get_signkey_usage_vk:
  {|crypto_usages|} ->
  sk:bytes ->
  Lemma
  (ensures get_signkey_usage (vk sk) == get_usage sk)
  [SMTPat (get_signkey_usage (vk sk))]
let get_signkey_usage_vk #cusages sk =
  normalize_term_spec vk;
  normalize_term_spec get_signkey_usage

val bytes_invariant_sign:
  {|crypto_invariants|} -> tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    bytes_invariant tr sk /\
    SigKey? (get_usage sk) /\
    sign_pred tr (vk sk) msg
  )
  (ensures bytes_invariant tr (sign sk nonce msg))
  [SMTPat (bytes_invariant tr (sign sk nonce msg))]
let bytes_invariant_sign #cinvs tr sk nonce msg =
  normalize_term_spec sign;
  normalize_term_spec vk;
  normalize_term_spec bytes_invariant

val get_label_sign:
  {|crypto_usages|} ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label (sign sk nonce msg) == get_label msg)
  [SMTPat (get_label (sign sk nonce msg))]
let get_label_sign #cusages sk nonce msg =
  normalize_term_spec sign;
  normalize_term_spec get_label

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
      sign_pred tr vk msg
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

[@@"opaque_to_smt"]
val hash: bytes -> bytes
let hash msg = Hash msg

// Lemma for attacker knowledge theorem
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

// Lemmas for the user
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

val get_label_hash:
  {|crypto_usages|} ->
  msg:bytes ->
  Lemma (get_label (hash msg) == get_label msg)
  [SMTPat (get_label (hash msg))]
let get_label_hash #cusages msg =
  normalize_term_spec hash;
  normalize_term_spec get_label

val hash_injective:
  msg1:bytes -> msg2:bytes ->
  Lemma
  (requires hash msg1 == hash msg2)
  (ensures msg1 == msg2)
  // No SMTPat, call this manually because it's an important argument of the proof?
let hash_injective msg1 msg2 =
  normalize_term_spec hash
