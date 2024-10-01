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

  dh_usage = {
    known_peer_usage = (fun usg1 usg2 ->
      match usg1, usg2 with
      | DhKey "DH.dh_key" _, _ -> AeadKey "DH.aead_key" empty
      | _, DhKey "DH.dh_key" _ -> AeadKey "DH.aead_key" empty
      | _, _ -> NoUsage
    );
    unknown_peer_usage = (fun usg1 -> 
      match usg1 with
      | DhKey "DH.dh_key" _ -> AeadKey "DH.aead_key" empty
      | _ -> NoUsage);
    known_peer_usage_commutes = (fun usg1 usg2 -> ());
    unknown_peer_usage_implies = (fun usg1 usg2 -> ());
  }
}

#push-options "--ifuel 2 --fuel 0"
val dh_crypto_preds: crypto_predicates
let dh_crypto_preds = {
  default_crypto_predicates with

  sign_pred = {
    pred = (fun tr vk sig_msg ->
      (exists prin. get_signkey_usage vk == long_term_key_type_to_usage (LongTermSigKey "DH.SigningKey") prin /\ (
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
    pred_later = (fun tr1 tr2 vk msg -> ());
  };
}
#pop-options

instance dh_crypto_invs: crypto_invariants = {
  usages = dh_crypto_usages;
  preds = dh_crypto_preds;
}

(*** Proofs ***)

val compute_message1_proof:
  tr:trace ->
  alice:principal -> bob:principal -> x:bytes ->
  Lemma
    (requires
      event_triggered tr alice (Initiate1 alice bob x) /\
      bytes_invariant tr x /\
      DhKey? (get_usage x)
    )
    (ensures 
      is_publishable tr (compute_message1 alice x)
    )
let compute_message1_proof tr alice bob x =
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
  assert(get_label tr msgb `can_flow tr` public);
  assert(is_publishable tr msgb);
  ()

val decode_message1_proof:
  tr:trace ->
  msg1_bytes:bytes ->
  Lemma
  (requires is_publishable tr msg1_bytes)
  (ensures (
    match decode_message1 msg1_bytes with
    | Some msg1 -> (
      is_publishable tr msg1.gx
    )
    | None -> True
  ))
let decode_message1_proof tr msg1_bytes =
  match decode_message1 msg1_bytes with
    | Some msg1 -> (
      // This lemma
      // - requires that msg_bytes is publishable
      // - ensures that `msg1.gx` is publishable
      //   (`msg1` being the result of parsing `msg_bytes` to the type `message1`)
      parse_wf_lemma message (is_publishable tr) msg1_bytes;
      
      // The following code is not needed for the proof.
      // It just shows what we need to show to prove the lemma.
      assert(bytes_invariant tr msg1.gx);
      assert(get_label tr msg1.gx `can_flow tr` public);
      ()
    )
    | None -> ()

val compute_message2_proof:
  tr:trace -> 
  alice:principal -> bob:principal ->
  gx:bytes -> y:bytes ->
  sk_b:bytes -> n_sig:bytes ->
  Lemma
  (requires
    event_triggered tr bob (Respond1 alice bob gx (dh_pk y) y) /\
    is_publishable tr gx /\
    bytes_invariant tr y /\
    is_private_key_for tr sk_b (LongTermSigKey "DH.SigningKey") bob /\
    is_secret (principal_label bob) tr n_sig /\
    SigNonce? (get_usage n_sig)
  )
  (ensures
    is_publishable tr (compute_message2 alice bob gx (dh_pk y) sk_b n_sig)
  )
let compute_message2_proof tr alice bob gx y sk_b n_sig =
  // Proof that the SigMsg2 is publishable
  // From the precondition we know that
  // msg1.gx and gy are publishable.
  let gy = dh_pk y in
  let sig_msg = SigMsg2 {alice; gx; gy} in
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
  assert(is_publishable tr (compute_message2 alice bob gx gy sk_b n_sig));
  ()

#push-options "--ifuel 1 --z3rlimit 20"
val decode_and_verify_message2_proof:
  tr:trace ->
  msg2_bytes:bytes ->
  alice:principal -> alice_si:state_id -> bob:principal ->
  x:bytes -> pk_b:bytes ->
  Lemma
  (requires
    is_publishable tr msg2_bytes /\
    is_secret (principal_state_label alice alice_si) tr x /\
    is_public_key_for tr pk_b (LongTermSigKey "DH.SigningKey") bob
  )
  (ensures (
    match decode_and_verify_message2 msg2_bytes alice x pk_b with
    | Some res -> (
      let sig_msg = SigMsg2 {alice; gx=(dh_pk x); gy=res.gy} in
      is_publishable tr res.gy /\
      (is_corrupt tr (principal_label bob) \/
      (exists y. event_triggered tr bob (Respond1 alice bob (dh_pk x) res.gy y)))
    )
    | None -> True
  ))
let decode_and_verify_message2_proof tr msg2_bytes alice alice_si bob x pk_b =
  match decode_and_verify_message2 msg2_bytes alice x pk_b with
    | Some res -> (
      parse_wf_lemma message (is_publishable tr) msg2_bytes;
      let gx = dh_pk x in
      let gy = res.gy in
      serialize_wf_lemma sig_message (bytes_invariant tr) (SigMsg2 {alice; gx; gy});

      // The following code is not needed for the proof.
      // It just shows what we need to show to prove the lemma.
      assert(is_publishable tr res.gy);
      
      assert(
        is_corrupt tr (principal_label bob) \/
        (exists y. res.gy == dh_pk y /\ event_triggered tr bob (Respond1 alice bob gx gy y))
      );
      ()
    )
    | None -> ()
#pop-options

val compute_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal ->
  gx:bytes -> gy:bytes -> x:bytes ->
  sk_a:bytes -> n_sig:bytes ->
  Lemma
  (requires
    event_triggered tr alice (Initiate2 alice bob (dh_pk x) gy (dh x gy)) /\
    is_publishable tr gx /\ is_publishable tr gy /\
    gx = dh_pk x /\
    is_private_key_for tr sk_a (LongTermSigKey "DH.SigningKey") alice /\
    is_secret (principal_label alice) tr n_sig /\
    SigNonce? (get_usage n_sig)
  )
  (ensures
    is_publishable tr (compute_message3 alice bob (dh_pk x) gy sk_a n_sig)
  )
let compute_message3_proof tr alice bob gx gy x sk_a n_sig =
  let sig_msg = SigMsg3 {bob; gx; gy} in
  serialize_wf_lemma sig_message (is_publishable tr) sig_msg;
  
  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(is_publishable tr (serialize sig_message sig_msg));
  let sg = sign sk_a n_sig (serialize sig_message sig_msg) in 

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma. 
  assert(get_label tr sg `can_flow tr` public);
  assert(bytes_invariant tr sg);
  assert(is_publishable tr sg);

  let msg = Msg3 {sg} in
  serialize_wf_lemma message (is_publishable tr) msg;

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(is_publishable tr (serialize message msg));
  ()

#push-options "--ifuel 1 --z3rlimit 25"
val decode_and_verify_message3_proof:
  tr:trace ->
  msg3_bytes:bytes ->
  alice:principal -> bob:principal -> bob_si:state_id ->
  gx:bytes -> y:bytes -> pk_a:bytes ->
  Lemma
  (requires
    is_publishable tr msg3_bytes /\
    is_publishable tr gx /\
    is_secret (principal_state_label bob bob_si) tr y /\
    is_public_key_for tr pk_a (LongTermSigKey "DH.SigningKey") alice
  )
  (ensures (
    let gy = dh_pk y in
    match decode_and_verify_message3 msg3_bytes bob gx gy y pk_a with
    | Some res -> (
      let sig_msg = SigMsg3 {bob; gx; gy} in
      (is_corrupt tr (principal_label alice) \/
      (exists x. gx == dh_pk x /\ event_triggered tr alice (Initiate2 alice bob gx gy (dh x gy))))
    )
    | None -> True
  ))
let decode_and_verify_message3_proof tr msg3_bytes alice bob bob_si gx y pk_a =
  let gy = dh_pk y in
  match decode_and_verify_message3 msg3_bytes bob gx gy y pk_a with
    | Some res -> (
      parse_wf_lemma message (is_publishable tr) msg3_bytes;
      serialize_wf_lemma sig_message (is_publishable tr) (SigMsg3 {bob; gx; gy});
      ()
    )
    | None -> ()
#pop-options
