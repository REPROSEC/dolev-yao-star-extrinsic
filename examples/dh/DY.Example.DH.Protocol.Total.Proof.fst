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
        exists y. sig_msg2.gy == (dh_pk y) /\ event_triggered tr prin (Respond1 sig_msg2.a prin sig_msg2.gx sig_msg2.gy y)
      )
      | Some (SigMsg3 sig_msg3) -> (
        exists x k. sig_msg3.gx == (dh_pk x) /\ event_triggered tr prin (Initiate2 prin sig_msg3.b sig_msg3.gx sig_msg3.gy k)
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
    (ensures 
      is_publishable tr (compute_message1 alice x) /\
      (exists gx. gx == dh_pk x /\ is_publishable tr gx)
    )
let compute_message1_proof tr alice bob x si =
  let gx = dh_pk x in
  assert(is_publishable tr gx);
  let msg = Msg1 {alice; gx} in

  // This lemma makes sure that the second argument
  // (is_publishable tr) is true for the third argument
  // (msg) before and after serialization. Without
  // this lemma we would loose all the guarantees about
  // the bytes after the message was serialized.
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
      // The second argument of the lemma parse_wf_lemma is a predicate defined
      // on bytes (is_publishable tr).
      // The lemma has the precondition that the predicate is true if the
      // third argument is applied to the predicate.
      // It then makes sure that the predicate is also true after
      // parsing the third argument from bytes into a data type (message).
      parse_wf_lemma message (is_publishable tr) msg_bytes;
      
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
    event_triggered tr bob (Respond1 alice bob msg1.gx gy y) /\
    is_publishable tr msg1.gx /\ is_publishable tr gy /\
    gy == dh_pk y /\
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
  //assert(is_publishable tr sig_msg_bytes);
  let sg = sign sk_b n_sig sig_msg_bytes in
  
  (*assert(bytes_invariant tr sk_b);
  assert(bytes_invariant tr n_sig);
  assert(bytes_invariant tr sig_msg_bytes);
  assert(get_usage sk_b == SigKey "DH.SigningKey");
  assert(is_secret (principal_label bob) tr sk_b);
  assert(SigKey? (get_usage sk_b));*)
  
  // The reveal_opaques is needed to look into the definition
  // of get_signkey_usage and see that it simply calls
  // get_usage on the given key.
  //reveal_opaque (`%get_signkey_usage) (get_signkey_usage);
  
  (*assert(SigKey? (get_signkey_usage (Vk sk_b)));
  assert(get_signkey_usage (Vk sk_b) == SigKey "DH.SigningKey");
  assert((SigMsg2?.msg sig_msg).gy == (dh_pk y));*)

  //reveal_opaque (`%get_signkey_label) (get_signkey_label);
  (*assert(exists prin. get_signkey_label (Vk sk_b) = principal_label prin /\
    (SigMsg2?.msg sig_msg).gy == (dh_pk y) /\ 
    event_triggered tr prin (Respond1 (SigMsg2?.msg sig_msg).a prin (SigMsg2?.msg sig_msg).gx (SigMsg2?.msg sig_msg).gy y));
  assert(dh_crypto_invs.preds.sign_pred tr (Vk sk_b) sig_msg_bytes) by (let open FStar.Tactics in dump "");
  assert(SigNonce? (get_usage n_sig));
  assert((get_label sig_msg_bytes) `can_flow tr` (get_label n_sig));
  
  assert(bytes_invariant tr sg);

  assert(is_publishable tr sg);*)
  let msg = Msg2 {bob; gy; sg} in
  serialize_wf_lemma message (is_publishable tr) msg;

  //let msg_bytes = compute_message2 alice bob msg1.gx gy sk_b n_sig in
  //assert(bytes_invariant tr msg_bytes);
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
      let sig_msg = SigMsg2 {a=alice; gx; gy=msg2.gy} in
      is_publishable tr msg2.gy /\
      is_publishable tr msg2.sg /\
      verify pk_b (serialize sig_message sig_msg) msg2.sg /\
      (is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
      (exists y. event_triggered tr bob (Respond1 alice bob gx msg2.gy y)))
    )
    | None -> True
  ))
let decode_message2_proof tr alice bob msg_bytes gx pk_b =
  match decode_message2 msg_bytes alice gx pk_b with
    | Some msg2 -> (
      parse_wf_lemma message (is_publishable tr) msg_bytes;
      //FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg_bytes;

      serialize_wf_lemma sig_message (bytes_invariant tr) (SigMsg2 {a=alice; gx; gy = msg2.gy});
      
      //reveal_opaque (`%verify) (verify);

      // Revealing a recursive function does not work with
      // ``reveal_opaque``. That's why we need to use
      // ``normalize_term_spec bytes_invariant;`` or 
      // ``norm_spec [zeta; delta_only [`%bytes_invariant]](bytes_invariant);``
      //normalize_term_spec bytes_invariant;

      (*assert(bytes_invariant tr msg_bytes);      
      assert(bytes_invariant tr msg2.sg);

      let sig_msg = SigMsg2 {a=alice; gx; gy=msg2.gy} in
      
      let sig_msg_bytes = serialize sig_message sig_msg in
      assert(verify pk_b sig_msg_bytes msg2.sg = true);
      
      let open DY.Core.Bytes.Type in
      let Sign sk nonce msg = msg2.sg in
      assert(msg = sig_msg_bytes);
      
      assert(is_publishable tr msg2.sg);
      assert(get_label msg2.sg `can_flow tr` get_label msg);
      assert(get_label msg2.sg `can_flow tr` public);
      
      
      normalize_term_spec get_label;

      assert(bytes_invariant tr msg);
      assert(is_publishable tr msg);
      
      FStar.Classical.move_requires (parse_wf_lemma sig_message (is_publishable tr)) msg;
      FStar.Classical.move_requires (parse_wf_lemma sig_message (bytes_invariant tr)) msg;

      assert(bytes_invariant tr gx);
      assert(bytes_invariant tr msg2.gy);
      
      assert(is_corrupt tr (principal_label alice) \/
        is_corrupt tr (principal_label bob) \/
        (exists y. msg2.gy == dh_pk y /\ event_triggered tr bob (Respond1 alice bob gx msg2.gy y))
      );*)
      ()
    )
    | None -> ()

val compute_message3_proof:
  tr:trace -> si:nat ->
  alice:principal -> bob:principal ->
  gx:bytes -> gy:bytes ->
  sk_a:bytes -> n_sig:bytes ->
  Lemma
  (requires
    (exists x k. event_triggered tr alice (Initiate2 alice bob gx gy k) /\ gx = dh_pk x) /\
    is_publishable tr gx /\ is_publishable tr gy /\
    is_signature_key "DH.SigningKey" (principal_label alice) tr sk_a /\
    is_secret (principal_label alice) tr n_sig /\
    SigNonce? (get_usage n_sig)
  )
  (ensures
    is_publishable tr (compute_message3 alice bob gx gy sk_a n_sig)
  )
let compute_message3_proof tr si alice bob gx gy sk_a n_sig =
  let sig_msg = SigMsg3 {b=bob; gx; gy} in
  serialize_wf_lemma sig_message (is_publishable tr) sig_msg;
  
  (* Debugging code
  assert(is_publishable tr (serialize sig_message sig_msg));*)
  let sg = sign sk_a n_sig (serialize sig_message sig_msg) in 

  (* Debugging code 
  assert(get_label sg `can_flow tr` public);
  assert(bytes_invariant tr sg);
  assert(is_publishable tr sg); *)

  let msg = Msg3 {sg} in
  serialize_wf_lemma message (is_publishable tr) msg;

  (* Debugging code
  assert(is_publishable tr (serialize message msg));*)
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
      let sig_msg = SigMsg3 {b=bob; gx; gy} in
      is_publishable tr msg3.sg /\
      verify pk_a (serialize sig_message sig_msg) msg3.sg /\
      (is_corrupt tr (principal_label alice) \/
      (exists x k. gx == dh_pk x /\ event_triggered tr alice (Initiate2 alice bob gx gy k)))
    )
    | None -> True
  ))
let decode_message3_proof tr alice bob gx gy msg_bytes pk_a =
  match decode_message3 msg_bytes bob gx gy pk_a with
    | Some msg3 -> (
      parse_wf_lemma message (is_publishable tr) msg_bytes;
      serialize_wf_lemma sig_message (is_publishable tr) (SigMsg3 {b=bob; gx; gy});
      ()
    )
    | None -> ()