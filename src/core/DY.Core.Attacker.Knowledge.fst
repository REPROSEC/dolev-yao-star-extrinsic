module DY.Core.Attacker.Knowledge

open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.Invariant
open DY.Core.Label.Type
open DY.Core.Label

#set-options "--fuel 1 --ifuel 0"

/// This modules defines the knowledge of the attacker,
/// and the attacker knowledge theorem
/// stating that an attacker only knows publishable value.
///
/// This is a crucial theorem for confidentiality proofs:
/// if the attacker knows a secret bytestring,
/// we deduce that the bytestring is publishable (attacker knowledge theorem),
/// meaning that its label flows to public (by definition of publishability),
/// which in turn will imply that some set of principals have been compromised (property of labels).

/// Auxillary prediate for the attacker knowledge:
/// given a trace `tr`,
/// can the attacker compute `msg`
/// by applying at most `step` cryptographic functions?

val attacker_knows_aux: nat -> trace -> bytes -> prop
let rec attacker_knows_aux step tr msg =
  // In zero steps, the attacker knows:
  if step = 0 then (
    // - messages sent on the network
    (
      msg_sent_on_network tr msg
    ) \/
    // - states that the attacker has corrupt
    (
      exists prin sess_id.
        state_was_corrupt tr prin sess_id msg
    ) \/
    // - public literals
    (
      exists lit.
        msg == literal_to_bytes lit
    )
  // The attacker can compute each cryptographic function in one step.
  ) else (
    // Use less steps (not super useful, but why not)
    attacker_knows_aux (step-1) tr msg \/
    // Concatenation
    (
      exists b1 b2.
        msg == concat b1 b2 /\
        attacker_knows_aux (step-1) tr b1 /\
        attacker_knows_aux (step-1) tr b2
    ) \/ (
      exists i b2 buf.
        Some (msg, b2) == split buf i /\
        attacker_knows_aux (step-1) tr buf
    ) \/ (
      exists i b1 buf.
        Some (b1, msg) == split buf i /\
        attacker_knows_aux (step-1) tr buf
    ) \/
    // AEAD
    (
      exists key nonce buf ad.
        msg == aead_enc key nonce buf ad /\
        attacker_knows_aux (step-1) tr key /\
        attacker_knows_aux (step-1) tr nonce /\
        attacker_knows_aux (step-1) tr buf /\
        attacker_knows_aux (step-1) tr ad
    ) \/ (
      exists key nonce buf ad.
        Some msg == aead_dec key nonce buf ad /\
        attacker_knows_aux (step-1) tr key /\
        attacker_knows_aux (step-1) tr nonce /\
        attacker_knows_aux (step-1) tr buf /\
        attacker_knows_aux (step-1) tr ad
    ) \/
    // Public-key encryption
    (
      exists sk.
        msg == pk sk /\
        attacker_knows_aux (step-1) tr sk
    ) \/ (
      exists pk nonce buf.
        msg == pke_enc pk nonce buf /\
        attacker_knows_aux (step-1) tr pk /\
        attacker_knows_aux (step-1) tr nonce /\
        attacker_knows_aux (step-1) tr buf
    ) \/ (
      exists sk buf.
        Some msg == pke_dec sk buf /\
        attacker_knows_aux (step-1) tr sk /\
        attacker_knows_aux (step-1) tr buf
    ) \/
    // Signature
    (
      exists sk.
        msg == vk sk /\
        attacker_knows_aux (step-1) tr sk
    ) \/ (
      exists sk nonce buf.
        msg == sign sk nonce buf /\
        attacker_knows_aux (step-1) tr sk /\
        attacker_knows_aux (step-1) tr nonce /\
        attacker_knows_aux (step-1) tr buf
    ) \/
    // Hash
    (
      exists buf.
        msg == hash buf /\
        attacker_knows_aux (step-1) tr buf
    ) \/
    // Diffie-Hellman
    (
      exists sk.
        msg == dh_pk sk /\
        attacker_knows_aux (step-1) tr sk
    ) \/ (
      exists sk pk.
        msg == dh sk pk /\
        attacker_knows_aux (step-1) tr sk /\
        attacker_knows_aux (step-1) tr pk
    ) \/
    // KDF
    (
      exists salt ikm.
        msg == kdf_extract salt ikm /\
        attacker_knows_aux (step-1) tr salt /\
        attacker_knows_aux (step-1) tr ikm
    ) \/ (
      exists prk info len.
        msg == kdf_expand prk info len /\
        attacker_knows_aux (step-1) tr prk /\
        attacker_knows_aux (step-1) tr info
    ) \/ (
      exists prk info len1 len2.
        len1 <= len2 /\
        msg == kdf_expand prk info len1 /\
        attacker_knows_aux (step-1) tr (kdf_expand prk info len2)
    ) \/
    // KEM
    (
      exists sk.
        msg == kem_pk sk /\
        attacker_knows_aux (step-1) tr sk
    ) \/ (
      exists pk nonce rhs.
        (msg, rhs) == kem_encap pk nonce /\
        attacker_knows_aux (step-1) tr pk /\
        attacker_knows_aux (step-1) tr nonce
    ) \/ (
      exists pk nonce lhs.
        (lhs, msg) == kem_encap pk nonce /\
        attacker_knows_aux (step-1) tr pk /\
        attacker_knows_aux (step-1) tr nonce
    ) \/ (
      exists sk encap.
        Some msg == kem_decap sk encap /\
        attacker_knows_aux (step-1) tr sk /\
        attacker_knows_aux (step-1) tr encap
    )
  )

/// The predicate for attacker knowledge:
/// given a trace `tr`,
/// can the attacker compute a bytestring `msg`
/// in any number of steps?

[@@ "opaque_to_smt"]
val attacker_knows: trace -> bytes -> prop
let attacker_knows tr msg =
  exists step. attacker_knows_aux step tr msg

/// Lemma for the base case of the attacker knowledge theorem:
/// bytestrings that the attacker obtained by corruption
/// are publishable.

val corrupted_state_is_publishable:
  {|protocol_invariants|} ->
  tr:trace -> prin:principal -> sess_id:state_id -> content:bytes ->
  Lemma
  (requires
    state_was_corrupt tr prin sess_id content /\
    trace_invariant tr
  )
  (ensures is_publishable tr content)
let corrupted_state_is_publishable #invs tr prin sess_id content =
  state_is_knowable_by tr prin sess_id content;
  state_pred_label_can_flow_public tr (principal_state_content_label_input prin sess_id content)

#push-options "--z3rlimit 25"
val attacker_only_knows_publishable_values_aux:
  {|protocol_invariants|} ->
  step:nat -> tr:trace -> msg:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows_aux step tr msg
  )
  (ensures is_publishable tr msg)
let rec attacker_only_knows_publishable_values_aux #invs step tr msg =
  if step = 0 then (
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (msg_sent_on_network_are_publishable tr));
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (msg_sent_on_network_are_publishable tr));
    FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 (corrupted_state_is_publishable tr));
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (literal_to_bytes_is_publishable tr))
  ) else (
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (attacker_only_knows_publishable_values_aux (step-1) tr));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (concat_preserves_publishability tr));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (split_preserves_publishability tr));
    FStar.Classical.forall_intro_4 (FStar.Classical.move_requires_4 (aead_enc_preserves_publishability tr));
    FStar.Classical.forall_intro_4 (FStar.Classical.move_requires_4 (aead_dec_preserves_publishability tr));
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (pk_preserves_publishability tr));
    FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 (pke_enc_preserves_publishability tr));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (pke_dec_preserves_publishability tr));
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (vk_preserves_publishability tr));
    FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 (sign_preserves_publishability tr));
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (hash_preserves_publishability tr));
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (dh_pk_preserves_publishability tr));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (dh_preserves_publishability tr));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (kdf_extract_preserves_publishability tr));
    FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 (kdf_expand_preserves_publishability tr));
    FStar.Classical.forall_intro_4 (FStar.Classical.move_requires_4 (kdf_expand_shorter_preserves_publishability tr));
    FStar.Classical.forall_intro   (FStar.Classical.move_requires   (kem_pk_preserves_publishability tr));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (kem_encap_preserves_publishability tr));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (kem_decap_preserves_publishability tr));
    ()
  )
#pop-options

/// In a trace that satisfy the trace invariant,
/// every bytestring known by the attacker is publishable.

val attacker_only_knows_publishable_values:
  {|protocol_invariants|} ->
  tr:trace -> msg:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr msg
  )
  (ensures is_publishable tr msg)
let attacker_only_knows_publishable_values #invs tr msg =
  reveal_opaque (`%attacker_knows) (attacker_knows);
  eliminate exists step. attacker_knows_aux step tr msg
  returns is_publishable tr msg
  with _. (
    attacker_only_knows_publishable_values_aux step tr msg
  )
