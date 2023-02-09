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
type protocol_preds = {
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

val bytes_invariant: protocol_preds -> trace -> bytes -> prop
let rec bytes_invariant pr tr b =
  match b with
  | Literal buf ->
    True
  | Rand label len time ->
    event_at tr RandGen time
  | Concat left right ->
    bytes_invariant pr tr left /\
    bytes_invariant pr tr right
  | Aead key nonce msg ad ->
    bytes_invariant pr tr key /\
    bytes_invariant pr tr nonce /\
    bytes_invariant pr tr msg /\
    bytes_invariant pr tr ad /\
    (get_label nonce) `can_flow tr` public /\
    (get_label ad) `can_flow tr` public /\
    (
      (
        // Honest case
        pr.aead_pred tr key nonce msg ad /\
        (get_label msg) `can_flow tr` (get_label key)
      ) \/ (
        // Attacker case
        (get_label key) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Pk sk ->
    bytes_invariant pr tr sk
  | PkEnc pk nonce msg ->
    bytes_invariant pr tr pk /\
    bytes_invariant pr tr nonce /\
    bytes_invariant pr tr msg /\
    (
      (
        // Honest case
        (get_label msg) `can_flow tr` (get_sk_label pk) /\
        (get_label msg) `can_flow tr` (get_label nonce) /\
        pr.pkenc_pred tr pk msg
      ) \/ (
        // Attacker case
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )
  | Vk sk ->
    bytes_invariant pr tr sk
  | Sign sk nonce msg ->
    bytes_invariant pr tr sk /\
    bytes_invariant pr tr nonce /\
    bytes_invariant pr tr msg /\
    (
      (
        // Honest case
        pr.sign_pred tr (Vk sk) msg
      ) \/ (
        // Attacker case
        (get_label sk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label msg) `can_flow tr` public
      )
    )

val bytes_invariant_later:
  preds:protocol_preds ->
  tr1:trace -> tr2:trace -> msg:bytes ->
  Lemma
  (requires bytes_invariant preds tr1 msg /\ tr1 <$ tr2)
  (ensures bytes_invariant preds tr2 msg)
  [SMTPat (bytes_invariant preds tr1 msg); SMTPat (tr1 <$ tr2)]
let rec bytes_invariant_later preds tr1 tr2 msg =
  match msg with
  | Literal buf -> ()
  | Rand label len time -> ()
  | Concat left right ->
    bytes_invariant_later preds tr1 tr2 left;
    bytes_invariant_later preds tr1 tr2 right
  | Aead key nonce msg ad ->
    FStar.Classical.move_requires (preds.aead_pred_later tr1 tr2 key nonce msg) ad;
    bytes_invariant_later preds tr1 tr2 key;
    bytes_invariant_later preds tr1 tr2 nonce;
    bytes_invariant_later preds tr1 tr2 msg;
    bytes_invariant_later preds tr1 tr2 ad
  | Pk sk ->
    bytes_invariant_later preds tr1 tr2 sk
  | PkEnc pk nonce msg ->
    FStar.Classical.move_requires (preds.pkenc_pred_later tr1 tr2 pk) msg;
    bytes_invariant_later preds tr1 tr2 pk;
    bytes_invariant_later preds tr1 tr2 nonce;
    bytes_invariant_later preds tr1 tr2 msg
  | Vk sk ->
    bytes_invariant_later preds tr1 tr2 sk
  | Sign sk nonce msg ->
    bytes_invariant_later preds tr1 tr2 sk;
    bytes_invariant_later preds tr1 tr2 nonce;
    bytes_invariant_later preds tr1 tr2 msg;
    FStar.Classical.move_requires (preds.sign_pred_later tr1 tr2 (Vk sk)) msg

(*** Various predicates ***)

val is_publishable: protocol_preds -> trace -> bytes -> prop
let is_publishable pr tr b =
  bytes_invariant pr tr b /\ (get_label b) `can_flow tr` public

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
  pr:protocol_preds -> tr:trace ->
  lit:FStar.Seq.seq FStar.UInt8.t ->
  Lemma
  (is_publishable pr tr (literal_to_bytes lit))
let literal_is_to_bytes_publishable pr tr lit = ()

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
  pr:protocol_preds -> tr:trace ->
  b1:bytes -> b2:bytes ->
  Lemma
  (requires is_publishable pr tr b1 /\ is_publishable pr tr b2)
  (ensures is_publishable pr tr (concat b1 b2))
let concat_preserves_publishability pr tr b1 b2 =
  ()

// Lemma for attacker knowledge theorem
val split_preserves_publishability:
  pr:protocol_preds -> tr:trace ->
  b:bytes -> i:nat ->
  Lemma
  (requires is_publishable pr tr b)
  (ensures (
    match split b i with
    | None -> True
    | Some (b1, b2) -> is_publishable pr tr b1 /\ is_publishable pr tr b2
  ))
let split_preserves_publishability pr tr b i =
  ()

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
  pr:protocol_preds -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    is_publishable pr tr key /\
    is_publishable pr tr nonce /\
    is_publishable pr tr msg /\
    is_publishable pr tr ad
  )
  (ensures is_publishable pr tr (aead_enc key nonce msg ad))
let aead_enc_preserves_publishability pr tr key nonce msg ad = ()

// Lemma for attacker knowledge theorem
val aead_dec_preserves_publishability:
  pr:protocol_preds -> tr:trace ->
  key:bytes -> nonce:bytes -> msg:bytes -> ad:bytes ->
  Lemma
  (requires
    is_publishable pr tr key /\
    is_publishable pr tr nonce /\
    is_publishable pr tr msg /\
    is_publishable pr tr ad
  )
  (ensures (
    match aead_dec key nonce msg ad with
    | Some res -> is_publishable pr tr res
    | None -> True
  ))
let aead_dec_preserves_publishability pr tr key nonce msg ad =
  // F* needs the match for some reason?
  match aead_dec key nonce msg ad with
  | Some res -> ()
  | None -> ()

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
  pr:protocol_preds -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable pr tr sk)
  (ensures is_publishable pr tr (pk sk))
let pk_preserves_publishability pr tr sk = ()

// Lemma for attacker knowledge theorem
val pk_enc_preserves_publishability:
  pr:protocol_preds -> tr:trace ->
  pk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable pr tr pk /\
    is_publishable pr tr nonce /\
    is_publishable pr tr msg
  )
  (ensures is_publishable pr tr (pk_enc pk nonce msg))
let pk_enc_preserves_publishability pr tr pk nonce msg = ()

// Lemma for attacker knowledge theorem
val pk_dec_preserves_publishability:
  pr:protocol_preds -> tr:trace ->
  sk:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable pr tr sk /\
    is_publishable pr tr msg
  )
  (ensures (
    match pk_dec sk msg with
    | Some res -> is_publishable pr tr res
    | None -> True
  ))
let pk_dec_preserves_publishability pr tr sk msg = ()

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
  pr:protocol_preds -> tr:trace ->
  sk:bytes ->
  Lemma
  (requires is_publishable pr tr sk)
  (ensures is_publishable pr tr (vk sk))
let vk_preserves_publishability pr tr vk = ()

// Lemma for attacker knowledge theorem
val sign_preserves_publishability:
  pr:protocol_preds -> tr:trace ->
  sk:bytes -> nonce:bytes -> msg:bytes ->
  Lemma
  (requires
    is_publishable pr tr sk /\
    is_publishable pr tr nonce /\
    is_publishable pr tr msg
  )
  (ensures is_publishable pr tr (sign sk nonce msg))
let sign_preserves_publishability pr tr sk nonce msg = ()
