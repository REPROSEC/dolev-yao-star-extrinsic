module DY.Core.Bytes

open DY.Core.Bytes.Type
open DY.Core.Trace.Type
open DY.Core.Label.Type
open DY.Core.Label
open DY.Core.Label.Lattice

#set-options "--fuel 1 --ifuel 1"

val length: bytes -> nat
let rec length b =
  match b with
  | Literal buf ->
    Seq.length buf
  | Rand label len time ->
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

val get_label: bytes -> label
let rec get_label b =
  match b with
  | Literal buf ->
    public
  | Rand label len time ->
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

val get_sk_label: bytes -> label
let get_sk_label pk =
  match pk with
  | Pk sk -> get_label sk
  | _ -> public

val get_signkey_label: bytes -> label
let get_signkey_label pk =
  match pk with
  | Vk sk -> get_label sk
  | _ -> public

noeq
type crypto_predicates = {
  aead_pred: tr:trace -> key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes -> prop;
  aead_pred_later:
    tr1:trace -> tr2:trace ->
    key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
    Lemma
    (requires aead_pred tr1 key nonce msg ad /\ tr1 <$ tr2)
    (ensures aead_pred tr2 key nonce msg ad)
  ;

  pkenc_pred: tr:trace -> pk:bytes -> msg:bytes -> prop;
  pkenc_pred_later:
    tr1:trace -> tr2:trace ->
    pk:bytes -> msg:bytes ->
    Lemma
    (requires pkenc_pred tr1 pk msg /\ tr1 <$ tr2)
    (ensures pkenc_pred tr2 pk msg)
  ;

  sign_pred: tr:trace -> vk:bytes -> msg:bytes -> prop;
  sign_pred_later:
    tr1:trace -> tr2:trace ->
    vk:bytes -> msg:bytes ->
    Lemma
    (requires sign_pred tr1 vk msg /\ tr1 <$ tr2)
    (ensures sign_pred tr2 vk msg)
  ;

  // ...
}

val bytes_invariant: crypto_predicates -> trace -> bytes -> prop
let rec bytes_invariant cpreds tr b =
  match b with
  | Literal buf ->
    True
  | Rand label len time ->
    event_at tr time (RandGen label len)
  | Concat left right ->
    bytes_invariant cpreds tr left /\
    bytes_invariant cpreds tr right
  | Aead key nonce msg ad ->
    bytes_invariant cpreds tr key /\
    bytes_invariant cpreds tr nonce /\
    bytes_invariant cpreds tr msg /\
    bytes_invariant cpreds tr ad /\
    (get_label nonce) `can_flow tr` public /\
    (get_label ad) `can_flow tr` public /\
    (
      (
        // Honest case
        cpreds.aead_pred tr key nonce msg ad /\
        (get_label msg) `can_flow tr` (get_label key)
      ) \/ (
        // Attacker case
        (get_label key) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Pk sk ->
    bytes_invariant cpreds tr sk
  | PkEnc pk nonce msg ->
    bytes_invariant cpreds tr pk /\
    bytes_invariant cpreds tr nonce /\
    bytes_invariant cpreds tr msg /\
    (
      (
        // Honest case
        (get_label msg) `can_flow tr` (get_sk_label pk) /\
        (get_label msg) `can_flow tr` (get_label nonce) /\
        cpreds.pkenc_pred tr pk msg
      ) \/ (
        // Attacker case
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Vk sk ->
    bytes_invariant cpreds tr sk
  | Sign sk nonce msg ->
    bytes_invariant cpreds tr sk /\
    bytes_invariant cpreds tr nonce /\
    bytes_invariant cpreds tr msg /\
    (
      (
        // Honest case
        cpreds.sign_pred tr (Vk sk) msg
      ) \/ (
        // Attacker case
        (get_label sk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )

val bytes_invariant_later:
  cpreds:crypto_predicates ->
  tr1:trace -> tr2:trace -> msg:bytes ->
  Lemma
  (requires bytes_invariant cpreds tr1 msg /\ tr1 <$ tr2)
  (ensures bytes_invariant cpreds tr2 msg)
  [SMTPat (bytes_invariant cpreds tr1 msg); SMTPat (tr1 <$ tr2)]
let rec bytes_invariant_later cpreds tr1 tr2 msg =
  match msg with
  | Literal buf -> ()
  | Rand label len time -> ()
  | Concat left right ->
    bytes_invariant_later cpreds tr1 tr2 left;
    bytes_invariant_later cpreds tr1 tr2 right
  | Aead key nonce msg ad ->
    FStar.Classical.move_requires (cpreds.aead_pred_later tr1 tr2 key nonce msg) ad;
    bytes_invariant_later cpreds tr1 tr2 key;
    bytes_invariant_later cpreds tr1 tr2 nonce;
    bytes_invariant_later cpreds tr1 tr2 msg;
    bytes_invariant_later cpreds tr1 tr2 ad
  | Pk sk ->
    bytes_invariant_later cpreds tr1 tr2 sk
  | PkEnc pk nonce msg ->
    FStar.Classical.move_requires (cpreds.pkenc_pred_later tr1 tr2 pk) msg;
    bytes_invariant_later cpreds tr1 tr2 pk;
    bytes_invariant_later cpreds tr1 tr2 nonce;
    bytes_invariant_later cpreds tr1 tr2 msg
  | Vk sk ->
    bytes_invariant_later cpreds tr1 tr2 sk
  | Sign sk nonce msg ->
    bytes_invariant_later cpreds tr1 tr2 sk;
    bytes_invariant_later cpreds tr1 tr2 nonce;
    bytes_invariant_later cpreds tr1 tr2 msg;
    FStar.Classical.move_requires (cpreds.sign_pred_later tr1 tr2 (Vk sk)) msg

(*** Various predicates ***)

val is_knowable_by: crypto_predicates -> label -> trace -> bytes -> prop
let is_knowable_by cpreds lab tr b =
  bytes_invariant cpreds tr b /\ (get_label b) `can_flow tr` lab

val is_publishable: crypto_predicates -> trace -> bytes -> prop
let is_publishable cpreds tr b =
  is_knowable_by cpreds public tr b

val is_secret: crypto_predicates -> label -> trace -> bytes -> prop
let is_secret cpreds lab tr b =
  bytes_invariant cpreds tr b /\ (get_label b) == lab

val is_verification_key: crypto_predicates -> label -> trace -> bytes -> prop
let is_verification_key cpreds lab tr b =
  is_publishable cpreds tr b /\ (get_signkey_label b) == lab

val is_signature_key: crypto_predicates -> label -> trace -> bytes -> prop
let is_signature_key cpreds lab tr b =
  bytes_invariant cpreds tr b /\ (get_label b) == lab

val is_encryption_key: crypto_predicates -> label -> trace -> bytes -> prop
let is_encryption_key cpreds lab tr b =
  is_publishable cpreds tr b /\ (get_sk_label b) == lab

val is_decryption_key: crypto_predicates -> label -> trace -> bytes -> prop
let is_decryption_key cpreds lab tr b =
  bytes_invariant cpreds tr b /\ (get_label b) == lab

(*** Literal ***)

val literal_to_bytes: FStar.Seq.seq FStar.UInt8.t -> bytes
let literal_to_bytes lit =
  Literal lit

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
let literal_to_bytes_to_literal lit = ()

// Lemma for attacker knowledge theorem
val literal_to_bytes_is_publishable:
  cpreds:crypto_predicates -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (is_publishable cpreds tr (literal_to_bytes lit))
let literal_to_bytes_is_publishable cpreds tr lit = ()

// Lemma for the user
val bytes_to_literal_to_bytes:
  b:bytes ->
  Lemma (
    match bytes_to_literal b with
    | None -> True
    | Some lit -> b == literal_to_bytes lit
  )
let bytes_to_literal_to_bytes b = ()

val length_literal_to_bytes:
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma (length (literal_to_bytes lit) == FStar.Seq.length lit)
let length_literal_to_bytes lit = ()

val bytes_invariant_literal_to_bytes:
  cpreds:crypto_predicates -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (ensures bytes_invariant cpreds tr (literal_to_bytes lit))
  [SMTPat (bytes_invariant cpreds tr (literal_to_bytes lit))]
let bytes_invariant_literal_to_bytes cpreds tr lit = ()

(*** Concatenation ***)

val concat: bytes -> bytes -> bytes
let concat left right =
  Concat left right

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
let split_concat left right = ()

// Lemma for attacker knowledge theorem
val concat_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (requires is_publishable cpreds tr b1 /\ is_publishable cpreds tr b2)
  (ensures is_publishable cpreds tr (concat b1 b2))
let concat_preserves_publishability cpreds tr b1 b2 =
  ()

// Lemma for attacker knowledge theorem
val split_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  b:bytes -> i:nat ->
  Lemma
  (requires is_publishable cpreds tr b)
  (ensures (
    match split b i with
    | None -> True
    | Some (b1, b2) -> is_publishable cpreds tr b1 /\ is_publishable cpreds tr b2
  ))
let split_preserves_publishability cpreds tr b i =
  ()

// Lemma for the user
val concat_split:
  b:bytes -> i:nat ->
  Lemma (
    match split b i with
    | None -> True
    | Some (left, right) -> b == concat left right
  )
let concat_split b i = ()

val concat_length:
  left:bytes -> right:bytes ->
  Lemma
  (length (concat left right) = length left + length right)
let concat_length left right = ()

val split_length:
  b:bytes -> i:nat ->
  Lemma (
    match split b i with
    | None -> True
    | Some (b1, b2) -> length b1 == i /\ i + length b2 == length b
  )
let split_length b i = ()

val bytes_invariant_concat:
  cpreds:crypto_predicates -> tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (requires bytes_invariant cpreds tr b1 /\ bytes_invariant cpreds tr b2)
  (ensures bytes_invariant cpreds tr (concat b1 b2))
  [SMTPat (bytes_invariant cpreds tr (concat b1 b2))]
let bytes_invariant_concat cpreds tr b1 b2 = ()

val bytes_invariant_split:
  cpreds:crypto_predicates -> tr:trace ->
  b:bytes -> i:nat ->
  Lemma
  (requires bytes_invariant cpreds tr b)
  (ensures (
    match split b i with
    | None -> True
    | Some (b1, b2) -> bytes_invariant cpreds tr b1 /\ bytes_invariant cpreds tr b2
  ))
  [SMTPat (bytes_invariant cpreds tr b); SMTPat (split b i)]
let bytes_invariant_split cpreds tr b i =
  ()

val get_label_concat:
  b1:bytes -> b2:bytes ->
  Lemma
  (ensures get_label (concat b1 b2) == meet (get_label b1) (get_label b2))
  [SMTPat (get_label (concat b1 b2))]
let get_label_concat b1 b2 = ()

val concat_preserves_knowability:
  cpreds:crypto_predicates -> lab:label -> tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (requires is_knowable_by cpreds lab tr b1 /\ is_knowable_by cpreds lab tr b2)
  (ensures is_knowable_by cpreds lab tr (concat b1 b2))
  [SMTPat (is_knowable_by cpreds lab tr (concat b1 b2))]
let concat_preserves_knowability cpreds lab tr b1 b2 = ()

val split_preserves_knowability:
  cpreds:crypto_predicates -> lab:label -> tr:trace ->
  b:bytes -> i:nat ->
  Lemma
  (requires is_knowable_by cpreds lab tr b)
  (ensures (
    match split b i with
    | None -> True
    | Some (b1, b2) -> is_knowable_by cpreds lab tr b1 /\ is_knowable_by cpreds lab tr b2
  ))
let split_preserves_knowability cpreds lab tr b i = ()

(*** AEAD ***)

val aead_enc: bytes -> bytes -> bytes -> bytes -> bytes
let aead_enc key nonce msg ad =
  Aead key nonce msg ad

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
let aead_dec_enc key nonce msg ad = ()

// Lemma for attacker knowledge theorem
val aead_enc_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    is_publishable cpreds tr key /\
    is_publishable cpreds tr nonce /\
    is_publishable cpreds tr msg /\
    is_publishable cpreds tr ad
  )
  (ensures is_publishable cpreds tr (aead_enc key nonce msg ad))
let aead_enc_preserves_publishability cpreds tr key nonce msg ad = ()

// Lemma for attacker knowledge theorem
val aead_dec_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    is_publishable cpreds tr key /\
    is_publishable cpreds tr nonce /\
    is_publishable cpreds tr msg /\
    is_publishable cpreds tr ad
  )
  (ensures (
    match aead_dec key nonce msg ad with
    | Some res -> is_publishable cpreds tr res
    | None -> True
  ))
let aead_dec_preserves_publishability cpreds tr key nonce msg ad =
  // F* needs the match for some reason?
  match aead_dec key nonce msg ad with
  | Some res -> ()
  | None -> ()

val bytes_invariant_aead_enc:
  cpreds:crypto_predicates -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    bytes_invariant cpreds tr key /\
    bytes_invariant cpreds tr nonce /\
    bytes_invariant cpreds tr msg /\
    bytes_invariant cpreds tr ad /\
    (get_label nonce) `can_flow tr` public /\
    (get_label ad) `can_flow tr` public /\
    (get_label msg) `can_flow tr` (get_label key) /\
    cpreds.aead_pred tr key nonce msg ad
  )
  (ensures bytes_invariant cpreds tr (aead_enc key nonce msg ad))
  [SMTPat (bytes_invariant cpreds tr (aead_enc key nonce msg ad))]
let bytes_invariant_aead_enc cpreds tr key nonce msg ad = ()

val get_label_aead_enc:
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (ensures get_label (aead_enc key nonce msg ad) = public)
  [SMTPat (get_label (aead_enc key nonce msg ad))]
let get_label_aead_enc key nonce msg ad = ()

//TODO: is there a good reason for such a high rlimit?
#push-options "--z3rlimit 50"
val bytes_invariant_aead_dec:
  cpreds:crypto_predicates -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    // Actually only need the one on `msg`
    bytes_invariant cpreds tr key /\
    bytes_invariant cpreds tr nonce /\
    bytes_invariant cpreds tr msg /\
    bytes_invariant cpreds tr ad
  )
  (ensures (
    match aead_dec key nonce msg ad with
    | None -> True
    | Some plaintext -> (
      is_knowable_by cpreds (get_label key) tr plaintext /\
      (
        cpreds.aead_pred tr key nonce plaintext ad
        \/
        is_publishable cpreds tr key
      )
    )
  ))
  [SMTPat (aead_dec key nonce msg ad); SMTPat (bytes_invariant cpreds tr msg)]
let bytes_invariant_aead_dec cpreds tr key nonce msg ad = ()
#pop-options

(*** Public-key encryption ***)

val pk: bytes -> bytes
let pk sk = Pk sk

val pk_enc: bytes -> bytes -> bytes -> bytes
let pk_enc pk nonce msg =
  PkEnc pk nonce msg

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
let pk_dec_enc key nonce msg = ()

// Lemma for attacker knowledge theorem
val pk_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable cpreds tr sk)
  (ensures is_publishable cpreds tr (pk sk))
let pk_preserves_publishability cpreds tr sk = ()

// Lemma for attacker knowledge theorem
val pk_enc_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable cpreds tr pk /\
    is_publishable cpreds tr nonce /\
    is_publishable cpreds tr msg
  )
  (ensures is_publishable cpreds tr (pk_enc pk nonce msg))
let pk_enc_preserves_publishability cpreds tr pk nonce msg = ()

// Lemma for attacker knowledge theorem
val pk_dec_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable cpreds tr sk /\
    is_publishable cpreds tr msg
  )
  (ensures (
    match pk_dec sk msg with
    | Some res -> is_publishable cpreds tr res
    | None -> True
  ))
let pk_dec_preserves_publishability cpreds tr sk msg = ()

val bytes_invariant_pk:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant cpreds tr sk)
  (ensures bytes_invariant cpreds tr (pk sk))
  [SMTPat (bytes_invariant cpreds tr (pk sk))]
let bytes_invariant_pk cpreds tr sk = ()

val get_label_pk:
  sk:bytes ->
  Lemma
  (ensures get_label (pk sk) == public)
  [SMTPat (get_label (pk sk))]
let get_label_pk sk = ()

val bytes_invariant_pk_enc:
  cpreds:crypto_predicates -> tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant cpreds tr pk /\
    bytes_invariant cpreds tr nonce /\
    bytes_invariant cpreds tr msg /\
    (get_label msg) `can_flow tr` (get_sk_label pk) /\
    (get_label msg) `can_flow tr` (get_label nonce) /\
    cpreds.pkenc_pred tr pk msg
  )
  (ensures bytes_invariant cpreds tr (pk_enc pk nonce msg))
  [SMTPat (bytes_invariant cpreds tr (pk_enc pk nonce msg))]
let bytes_invariant_pk_enc cpreds tr pk nonce msg = ()

val get_label_pk_enc:
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label (pk_enc pk nonce msg) == public)
  [SMTPat (get_label (pk_enc pk nonce msg))]
let get_label_pk_enc pk nonce msg = ()

val bytes_invariant_pk_dec:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant cpreds tr sk /\
    bytes_invariant cpreds tr msg
  )
  (ensures (
    match pk_dec sk msg with
    | None -> True
    | Some plaintext ->
      is_knowable_by cpreds (get_label sk) tr plaintext /\
      (
        cpreds.pkenc_pred tr (pk sk) plaintext
        \/
        is_publishable cpreds tr plaintext
      )
  ))
  [SMTPat (pk_dec sk msg); SMTPat (bytes_invariant cpreds tr msg)]
let bytes_invariant_pk_dec cpreds tr sk msg = ()

(*** Signature ***)

val vk: bytes -> bytes
let vk sk = Vk sk

val sign: bytes -> bytes -> bytes -> bytes
let sign sk nonce msg =
  Sign sk nonce msg

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
  (verify (vk sk) msg (Sign sk nonce msg))
let verify_sign sk nonce msg = ()

// Lemma for attacker knowledge theorem
val vk_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable cpreds tr sk)
  (ensures is_publishable cpreds tr (vk sk))
let vk_preserves_publishability cpreds tr vk = ()

// Lemma for attacker knowledge theorem
val sign_preserves_publishability:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable cpreds tr sk /\
    is_publishable cpreds tr nonce /\
    is_publishable cpreds tr msg
  )
  (ensures is_publishable cpreds tr (sign sk nonce msg))
let sign_preserves_publishability cpreds tr sk nonce msg = ()

val bytes_invariant_vk:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires bytes_invariant cpreds tr sk)
  (ensures bytes_invariant cpreds tr (pk sk))
  [SMTPat (bytes_invariant cpreds tr (pk sk))]
let bytes_invariant_vk cpreds tr sk = ()

val get_label_vk:
  sk:bytes ->
  Lemma
  (ensures get_label (vk sk) == public)
  [SMTPat (get_label (vk sk))]
let get_label_vk sk = ()

val bytes_invariant_sign:
  cpreds:crypto_predicates -> tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    bytes_invariant cpreds tr sk /\
    bytes_invariant cpreds tr nonce /\
    bytes_invariant cpreds tr msg /\
    bytes_invariant cpreds tr sk /\
    cpreds.sign_pred tr (vk sk) msg
  )
  (ensures bytes_invariant cpreds tr (sign sk nonce msg))
  [SMTPat (bytes_invariant cpreds tr (sign sk nonce msg))]
let bytes_invariant_sign cpreds tr sk nonce msg = ()

val get_label_sign:
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (ensures get_label (sign sk nonce msg) == get_label msg)
  [SMTPat (get_label (sign sk nonce msg))]
let get_label_sign sk nonce msg = ()

val bytes_invariant_verify:
  cpreds:crypto_predicates -> tr:trace ->
  vk:bytes -> msg:bytes -> signature:bytes ->
  Lemma
  (requires
    bytes_invariant cpreds tr vk /\
    bytes_invariant cpreds tr msg /\
    bytes_invariant cpreds tr signature /\
    verify vk msg signature
  )
  (ensures
    cpreds.sign_pred tr vk msg
    \/
    (get_signkey_label vk) `can_flow tr` public
  )
  [SMTPat (verify vk msg signature); SMTPat (bytes_invariant cpreds tr signature)]
let bytes_invariant_verify cpreds tr vk msg signature = ()
