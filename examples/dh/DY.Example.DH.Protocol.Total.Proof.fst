module DY.Example.DH.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total
open DY.Example.DH.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

val dh_crypto_usages: crypto_usages
instance dh_crypto_usages = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
val dh_crypto_preds: crypto_predicates dh_crypto_usages
let dh_crypto_preds = {
  default_crypto_predicates dh_crypto_usages with

  sign_pred = (fun tr vk sig_msg -> 
    get_signkey_usage vk == SigKey "DH.SigningKey" /\
    (exists prin. get_signkey_label vk = principal_label prin /\ (
      match parse sig_message sig_msg with
      | Some (SigMsg2 sig_msg2) -> (
        exists y. sig_msg2.gy == (dh_pk y) /\ event_triggered tr prin (Respond1 sig_msg2.a prin sig_msg2.gx sig_msg2.gy y)
      )
      | Some (SigMsg3 sig_msg3) -> (
        exists x. sig_msg3.gx == (dh_pk x) /\ event_triggered tr prin (Initiate2 prin sig_msg3.b sig_msg3.gx sig_msg3.gy x)
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
  alice:principal -> bob:principal -> x:bytes -> si:nat ->
  Lemma
    (requires
      event_triggered tr alice (Initiate1 alice bob x) /\
      is_secret (principal_state_label alice si) tr x /\
      DhKey? (get_usage x)
    )
    (ensures is_publishable tr (compute_message1 alice x))
let compute_message1_proof tr alice bob x si =
  let gx = dh_pk x in
  assert(is_publishable tr gx);
  let msg = Msg1 {alice; gx} in
  serialize_wf_lemma message (is_publishable tr) msg;

  // The following code is not needed for the prove.
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
  (requires bytes_invariant tr msg_bytes /\
    is_publishable tr msg_bytes)
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
      FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg_bytes;
      FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg_bytes;
      
      // Only for debugging purposes
      assert(bytes_invariant tr msg1.gx);
      assert(get_label msg1.gx `can_flow tr` public);
      ()
    )
    | None -> ()

val compute_message2_proof:
  tr:trace -> si:nat ->
  alice:principal -> bob:principal ->
  msg1:message1 ->
  gy:bytes -> y:bytes ->
  sk_b:bytes -> n_sig:bytes ->
  Lemma
  (requires
    event_triggered tr bob (Respond1 bob alice msg1.gx gy y) /\
    is_publishable tr msg1.gx /\ is_publishable tr gy /\
    is_secret (principal_state_label bob si) tr y /\
    is_signature_key "DH.SigningKey" (principal_label bob) tr sk_b /\
    is_secret (principal_label bob) tr n_sig /\
    SigNonce? (get_usage n_sig)
  )
  (ensures
    is_publishable tr (compute_message2 alice bob msg1.gx gy sk_b n_sig)
  )
let compute_message2_proof tr si alice bob msg1 gy y sk_b n_sig =
  let sig_msg = SigMsg2 {a=alice; gx=msg1.gx; gy} in
  serialize_wf_lemma sig_message (is_publishable tr) sig_msg;
  let sig_msg_bytes = serialize sig_message sig_msg in
  assert(is_publishable tr sig_msg_bytes);
  let sg = sign sk_b n_sig sig_msg_bytes in
  
  assert(bytes_invariant tr sk_b);
  assert(bytes_invariant tr n_sig);
  assert(bytes_invariant tr (serialize sig_message sig_msg));
  assume(SigKey? (get_signkey_usage (Vk sk_b)));
  assume(dh_crypto_invs.preds.sign_pred tr (Vk sk_b) sig_msg_bytes);
  assert(SigNonce? (get_usage n_sig));
  assert((get_label sig_msg_bytes) `can_flow tr` (get_label n_sig));

  assume((get_label sk_b) `can_flow tr` public);
  assume((get_label n_sig) `can_flow tr` public);
  assert((get_label sig_msg_bytes) `can_flow tr` public);
  
  assume(bytes_invariant tr sg);

  assert(is_publishable tr sg);
  let msg = Msg2 {bob; gy; sg} in
  serialize_wf_lemma message (is_publishable tr) msg;

  let msg_bytes = compute_message2 alice bob msg1.gx gy sk_b n_sig in
  assert(bytes_invariant tr msg_bytes);
  ()
