module DY.Example.DH.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total
open DY.Example.DH.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

val dh_crypto_usages: crypto_usages
instance dh_crypto_usages = {
  default_crypto_usages with

  dh_known_peer_usage = (fun s1 s2 ->
    match s1, s2 with
    | "DH.dh_key", _ -> AeadKey "DH.aead_key"
    | _, "DH.dh_key" -> AeadKey "DH.aead_key"
    | _, _ -> NoUsage
  );
  dh_unknown_peer_usage = (fun s1 -> 
    match s1 with
    | "DH.dh_key" -> AeadKey "DH.aead_key"
    | _ -> NoUsage);
  dh_known_peer_usage_commutes = (fun s1 s2 -> ());
  dh_unknown_peer_usage_implies = (fun s1 s2 -> ());
}

#push-options "--ifuel 2 --fuel 0"
val dh_crypto_preds: crypto_predicates dh_crypto_usages
let dh_crypto_preds = {
  default_crypto_predicates dh_crypto_usages with

  sign_pred = (fun tr vk sig_msg ->
    get_signkey_usage vk == SigKey "DH.SigningKey" /\
    (exists prin. get_signkey_label vk = principal_label prin /\ (
      match parse sig_message sig_msg with
      | Some (SigMsg2 sig_msg2) -> (
        exists y. sig_msg2.gy == (dh_pk y) /\ event_triggered tr prin (Respond1 sig_msg2.alice prin sig_msg2.gx sig_msg2.gy y)
      )
      | Some (SigMsg3 sig_msg3) -> (
        exists x. sig_msg3.gx == (dh_pk x) /\ event_triggered tr prin (Initiate2 prin sig_msg3.bob sig_msg3.gx sig_msg3.gy (dh x sig_msg3.gy))
      )
      | None -> False
    ))
  );
  sign_pred_later = (fun tr1 tr2 vk msg -> ())
}
#pop-options

instance dh_crypto_invs: crypto_invariants = {
  usages = dh_crypto_usages;
  preds = dh_crypto_preds;
}

(*** Proofs ***)

val compute_message1_proof:
  tr:trace ->
  alice:principal -> bob:principal -> x:bytes -> si:state_id ->
  Lemma
    (requires
      event_triggered tr alice (Initiate1 alice bob x) /\
      is_secret (principal_state_label alice si) tr x /\
      DhKey? (get_usage x)
    )
    (ensures 
      is_publishable tr (compute_message1 alice x)
    )
let compute_message1_proof tr alice bob x si =
  let gx = dh_pk x in
  assert(is_publishable tr gx);
  let msg = Msg1 {alice; gx} in

  // This lemma
  // - requires that msg.gx is is publishable
  // - ensures that `serialize _ msg` is publishable
  serialize_wf_lemma message (is_publishable tr) msg;

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  let msgb = compute_message1 alice x in 
  assert(bytes_invariant tr msgb);
  assert(get_label msgb `can_flow tr` public);
  assert(is_publishable tr msgb);
  ()

val decode_message1_proof:
  tr:trace ->
  alice:principal -> bob:principal ->
  msg_bytes:bytes ->
  Lemma
  (requires is_publishable tr msg_bytes)
  (ensures (
    match decode_message1 msg_bytes with
    | Some msg1 -> (
      is_publishable tr msg1.gx
    )
    | None -> True
  ))
let decode_message1_proof tr alice bob msg_bytes =
  match decode_message1 msg_bytes with
    | Some msg1 -> (
      // This lemma
      // - requires that msg_bytes is publishable
      // - ensures that `msg1.gx` is publishable
      //   (`msg1` being the result of parsing `msg_bytes` to the type `message1`)
      parse_wf_lemma message (is_publishable tr) msg_bytes;
      
      // The following code is not needed for the proof.
      // It just shows what we need to show to prove the lemma.
      assert(bytes_invariant tr msg1.gx);
      assert(get_label msg1.gx `can_flow tr` public);
      ()
    )
    | None -> ()

val compute_message2_proof:
  tr:trace -> si:state_id ->
  alice:principal -> bob:principal ->
  msg1:message1 -> y:bytes ->
  sk_b:bytes -> n_sig:bytes ->
  Lemma
  (requires (
    let gy = dh_pk y in
    event_triggered tr bob (Respond1 alice bob msg1.gx gy y) /\
    is_publishable tr msg1.gx /\ is_publishable tr gy /\
    gy == dh_pk y /\
    is_secret (principal_state_label bob si) tr y /\
    is_signature_key "DH.SigningKey" (principal_label bob) tr sk_b /\
    is_secret (principal_label bob) tr n_sig /\
    SigNonce? (get_usage n_sig)
    )
  )
  (ensures (
    let gy = dh_pk y in
    is_publishable tr (compute_message2 alice bob msg1.gx gy sk_b n_sig)
    )
  )
let compute_message2_proof tr si alice bob msg1 y sk_b n_sig =
  // Proof that the SigMsg2 is publishable
  // From the precondition we know that
  // msg1.gx and gy are publishable.
  let gy = dh_pk y in
  let sig_msg = SigMsg2 {alice; gx=msg1.gx; gy} in
  serialize_wf_lemma sig_message (is_publishable tr) sig_msg;
  let sig_msg_bytes = serialize sig_message sig_msg in

  // This assert is not needed for the proof
  // but shows that the serialized SigMsg2 is publishable.
  assert(is_publishable tr sig_msg_bytes);

  let sg = sign sk_b n_sig sig_msg_bytes in

  // This assert is not needed for the proof
  // but shows that the signature is also publishable.
  assert(is_publishable tr sg);
  
  // Since all parts of the Msg2 are publishable, we
  // can show that the serialized Msg2 is also publishable.
  let msg = Msg2 {bob; gy; sg} in
  serialize_wf_lemma message (is_publishable tr) msg;

  // This proves the post-condition
  assert(is_publishable tr (compute_message2 alice bob msg1.gx gy sk_b n_sig));
  ()

val decode_message2_proof:
  tr:trace ->
  alice:principal -> bob:principal ->
  msg_bytes:bytes -> gx:bytes -> pk_b:bytes ->
  Lemma
  (requires
    is_publishable tr msg_bytes /\
    is_publishable tr gx /\
    is_verification_key "DH.SigningKey" (principal_label bob) tr pk_b
  )
  (ensures (
    match decode_message2 msg_bytes alice gx pk_b with
    | Some msg2 -> (
      let sig_msg = SigMsg2 {alice; gx; gy=msg2.gy} in
      is_publishable tr msg2.gy /\
      is_publishable tr msg2.sg /\
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
      (exists y. event_triggered tr bob (Respond1 alice bob gx msg2.gy y)))
    )
    | None -> True
  ))
let decode_message2_proof tr alice bob msg_bytes gx pk_b =
  match decode_message2 msg_bytes alice gx pk_b with
    | Some msg2 -> (
      parse_wf_lemma message (is_publishable tr) msg_bytes;
      serialize_wf_lemma sig_message (bytes_invariant tr) (SigMsg2 {alice; gx; gy = msg2.gy});

      // The following code is not needed for the proof.
      // It just shows what we need to show to prove the lemma.
      assert(is_publishable tr msg2.sg);
      assert(is_publishable tr msg2.gy);
      
      assert(is_corrupt tr (principal_label alice) \/
        is_corrupt tr (principal_label bob) \/
        (exists y. msg2.gy == dh_pk y /\ event_triggered tr bob (Respond1 alice bob gx msg2.gy y))
      );
      ()
    )
    | None -> ()

val compute_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal ->
  gx:bytes -> gy:bytes ->
  sk_a:bytes -> n_sig:bytes ->
  Lemma
  (requires
    (exists x. event_triggered tr alice (Initiate2 alice bob gx gy (dh x gy)) /\ gx = dh_pk x) /\
    is_publishable tr gx /\ is_publishable tr gy /\
    is_signature_key "DH.SigningKey" (principal_label alice) tr sk_a /\
    is_secret (principal_label alice) tr n_sig /\
    SigNonce? (get_usage n_sig)
  )
  (ensures
    is_publishable tr (compute_message3 alice bob gx gy sk_a n_sig)
  )
let compute_message3_proof tr alice bob gx gy sk_a n_sig =
  let sig_msg = SigMsg3 {bob; gx; gy} in
  serialize_wf_lemma sig_message (is_publishable tr) sig_msg;
  
  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(is_publishable tr (serialize sig_message sig_msg));
  let sg = sign sk_a n_sig (serialize sig_message sig_msg) in 

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma. 
  assert(get_label sg `can_flow tr` public);
  assert(bytes_invariant tr sg);
  assert(is_publishable tr sg);

  let msg = Msg3 {sg} in
  serialize_wf_lemma message (is_publishable tr) msg;

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(is_publishable tr (serialize message msg));
  ()

val decode_message3_proof:
  tr:trace -> alice:principal -> bob:principal ->
  gx:bytes -> gy:bytes -> msg_bytes:bytes -> pk_a:bytes ->
  Lemma
  (requires
    is_publishable tr msg_bytes /\
    is_publishable tr gx /\
    is_publishable tr gy /\
    is_verification_key "DH.SigningKey" (principal_label alice) tr pk_a
  )
  (ensures (
    match decode_message3 msg_bytes bob gx gy pk_a with
    | Some msg3 -> (
      let sig_msg = SigMsg3 {bob; gx; gy} in
      is_publishable tr msg3.sg /\
      (is_corrupt tr (principal_label alice) \/
      (exists x. gx == dh_pk x /\ event_triggered tr alice (Initiate2 alice bob gx gy (dh x gy))))
    )
    | None -> True
  ))
let decode_message3_proof tr alice bob gx gy msg_bytes pk_a =
  match decode_message3 msg_bytes bob gx gy pk_a with
    | Some msg3 -> (
      parse_wf_lemma message (is_publishable tr) msg_bytes;
      serialize_wf_lemma sig_message (is_publishable tr) (SigMsg3 {bob; gx; gy});
      ()
    )
    | None -> ()
