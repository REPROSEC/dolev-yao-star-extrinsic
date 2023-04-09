module DY.Example.NSL.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Example.NSL.Protocol.Total
open DY.Example.NSL.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 2 --fuel 0"
let nsl_crypto_preds = {
  aead_pred = (fun tr key nonce msg ad -> False);
  aead_pred_later = (fun tr1 tr2 key nonce msg ad -> ());

  pkenc_pred = (fun tr pk msg ->
    (exists prin. get_sk_label pk = principal_label prin /\ (
      match parse message msg with
      | Some (Msg1 msg1) -> (
        let (alice, bob) = (msg1.alice, prin) in
        event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate1 alice bob msg1.n_a)) /\
        get_label msg1.n_a == join (principal_label alice) (principal_label bob)
      )
      | Some (Msg2 msg2) -> (
        let (alice, bob) = (prin, msg2.bob) in
        event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 alice bob msg2.n_a msg2.n_b)) /\
        get_label msg2.n_b == join (principal_label alice) (principal_label bob)
      )
      | Some (Msg3 msg3) -> (
        let bob = prin in
        exists alice n_a.
          get_label msg3.n_b `can_flow tr` (principal_label alice) /\
          event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a msg3.n_b))
      )
      | None -> False
    ))
  );
  pkenc_pred_later = (fun tr1 tr2 pk msg -> ());

  sign_pred = (fun tr vk msg -> False);
  sign_pred_later = (fun tr1 tr2 vk msg -> ());
}
#pop-options

val compute_message1_proof:
  tr:trace ->
  alice:principal -> bob:principal -> pk_b:bytes -> n_a:bytes -> nonce:bytes ->
  Lemma
  (requires
    // From the stateful code
    event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate1 alice bob n_a)) /\
    // From random generation
    is_secret nsl_crypto_preds (join (principal_label alice) (principal_label bob)) tr n_a  /\
    // From random generation
    is_secret nsl_crypto_preds (principal_label alice) tr nonce /\
    // From PKI invariants
    is_encryption_key nsl_crypto_preds (principal_label bob) tr pk_b
  )
  (ensures is_publishable nsl_crypto_preds tr (compute_message1 alice bob pk_b n_a nonce))
let compute_message1_proof tr alice bob pk_b n_a nonce =
  // trigger `join_eq` SMTPat
  assert (join (principal_label alice) (principal_label bob) `can_flow tr` join (principal_label alice) (principal_label bob));
  let msg = Msg1 {n_a; alice;} in
  serialize_wf_lemma message (is_knowable_by nsl_crypto_preds (principal_label alice) tr) msg;
  serialize_wf_lemma message (is_knowable_by nsl_crypto_preds (principal_label bob) tr) msg

// If bob successfully decrypt the first message,
// then n_a is knownable both by alice (in the message) and bob (the principal)
// This is because:
// - if the message was encrypted by the attacker, then n_a is publishable hence knowable by alice and bob
// - if the message was encrypted by an honest principal, this follows from the encryption predicate
#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message1_proof:
  tr:trace ->
  bob:principal -> msg_cipher:bytes -> sk_b:bytes ->
  Lemma
  (requires
    // From PrivateKeys invariants
    is_decryption_key nsl_crypto_preds (principal_label bob) tr sk_b /\
    // From the network
    bytes_invariant nsl_crypto_preds tr msg_cipher
  )
  (ensures (
    match decode_message1 bob msg_cipher sk_b with
    | None -> True
    | Some msg1 -> (
      is_knowable_by nsl_crypto_preds (join (principal_label msg1.alice) (principal_label bob)) tr msg1.n_a
    )
  ))
let decode_message1_proof tr bob msg_cipher sk_b =
  match decode_message1 bob msg_cipher sk_b with
  | None -> ()
  | Some msg1 ->
    let Some msg = pk_dec sk_b msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable nsl_crypto_preds tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant nsl_crypto_preds tr)) msg
#pop-options

val compute_message2_proof:
  tr:trace ->
  bob:principal -> msg1:message1 -> pk_a:bytes -> n_b:bytes -> nonce:bytes ->
  Lemma
  (requires
    // From the stateful code
    event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 msg1.alice bob msg1.n_a n_b)) /\
    // From decode_message1_proof
    is_knowable_by nsl_crypto_preds (join (principal_label msg1.alice) (principal_label bob)) tr msg1.n_a /\
    // From the random generation
    is_secret nsl_crypto_preds (join (principal_label msg1.alice) (principal_label bob)) tr n_b /\
    // From the random generation
    is_secret nsl_crypto_preds (principal_label bob) tr nonce /\
    // From the PKI
    is_encryption_key nsl_crypto_preds (principal_label msg1.alice) tr pk_a
  )
  (ensures
    is_publishable nsl_crypto_preds tr (compute_message2 bob msg1 pk_a n_b nonce)
  )
let compute_message2_proof tr bob msg1 pk_a n_b nonce =
  assert (join (principal_label msg1.alice) (principal_label bob) `can_flow tr` join (principal_label msg1.alice) (principal_label bob));
  let msg = Msg2 {n_a = msg1.n_a;  n_b; bob;} in
  serialize_wf_lemma message (is_knowable_by nsl_crypto_preds (principal_label msg1.alice) tr) msg;
  serialize_wf_lemma message (is_knowable_by nsl_crypto_preds (principal_label bob) tr) msg

// If alice successfully decrypt the second message,
// then n_b is knownable both by alice (in the message) and bob (the principal)
// (for the same reasons with decode_message1)
// Furthermore, either alice or bob are corrupt, or bob triggered the Respond1 event
// (proved with the encryption predicate)
#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message2_proof:
  tr:trace ->
  alice:principal -> bob:principal -> msg_cipher:bytes -> sk_a:bytes -> n_a:bytes ->
  Lemma
  (requires
    // From the NSL state invariant
    is_secret nsl_crypto_preds (join (principal_label alice) (principal_label bob)) tr n_a /\
    // From the PrivateKeys invariant
    is_decryption_key nsl_crypto_preds (principal_label alice) tr sk_a /\
    // From the network
    bytes_invariant nsl_crypto_preds tr msg_cipher
  )
  (ensures (
    match decode_message2 alice bob msg_cipher sk_a n_a with
    | None -> True
    | Some msg2 -> (
      is_knowable_by nsl_crypto_preds (join (principal_label alice) (principal_label bob)) tr msg2.n_b /\ (
      (principal_corrupt tr alice \/ principal_corrupt tr bob) \/ (
        event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 alice bob n_a msg2.n_b))
      )
      )
    )
  ))
let decode_message2_proof tr alice bob msg_cipher sk_a n_a =
  match decode_message2 alice bob msg_cipher sk_a n_a with
  | None -> ()
  | Some msg2 -> (
    let Some msg = pk_dec sk_a msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable nsl_crypto_preds tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant nsl_crypto_preds tr)) msg
  )
#pop-options

val compute_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal -> pk_b:bytes -> n_b:bytes -> nonce:bytes ->
  Lemma
  (requires
    // From the stateful code
    (exists n_a. event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b))) /\
    // From decode_message2_proof
    is_knowable_by nsl_crypto_preds (join (principal_label alice) (principal_label bob)) tr n_b /\
    // From the random generation
    is_secret nsl_crypto_preds (principal_label alice) tr nonce /\
    // From the PKI
    is_encryption_key nsl_crypto_preds (principal_label bob) tr pk_b
  )
  (ensures
    is_publishable nsl_crypto_preds tr (compute_message3 alice bob pk_b n_b nonce)
  )
let compute_message3_proof tr alice bob pk_b n_b nonce =
  assert (join (principal_label alice) (principal_label bob) `can_flow tr` join (principal_label alice) (principal_label bob));
  assert(exists alice n_a. event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b)));
  let msg = Msg3 {n_b;} in
  serialize_wf_lemma message (is_knowable_by nsl_crypto_preds (principal_label alice) tr) msg;
  serialize_wf_lemma message (is_knowable_by nsl_crypto_preds (principal_label bob) tr) msg;
  let msg3: message3 = {n_b;} in
  assert(msg3.n_b == n_b)

// If bob successfully decrypt the third message,
// Then either alice or bob are corrupt, or alice triggered the Initiate2 event
// (proved with the encryption predicate)
#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal -> msg_cipher:bytes -> sk_b:bytes -> n_b:bytes ->
  Lemma
  (requires
    // From the NSL state invariant
    get_label n_b = join (principal_label alice) (principal_label bob) /\
    // From the PrivateKeys invariant
    is_decryption_key nsl_crypto_preds (principal_label bob) tr sk_b /\
    // From the network
    bytes_invariant nsl_crypto_preds tr msg_cipher
  )
  (ensures (
    match decode_message3 alice bob msg_cipher sk_b n_b with
    | None -> True
    | Some msg3 -> (
      (principal_corrupt tr alice \/ principal_corrupt tr bob) \/ (
        (exists alice n_a.
          get_label msg3.n_b `can_flow tr` (principal_label alice) /\
          event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b)))
      )
    )
  ))
let decode_message3_proof tr alice bob msg_cipher sk_b n_b =
  match decode_message3 alice bob msg_cipher sk_b n_b with
  | None -> ()
  | Some msg3 -> (
    let Some msg = pk_dec sk_b msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable nsl_crypto_preds tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant nsl_crypto_preds tr)) msg
  )
#pop-options
