module DY.Core.Attacker.Knowledge

open FStar.List.Tot { for_allP, for_allP_eq }
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.Invariant
open DY.Core.Label.Type
open DY.Core.Label
open DY.Core.Attacker.Knowledge.Kleene

#set-options "--fuel 0 --ifuel 0"

/// This modules defines the knowledge of the attacker,
/// and the attacker knowledge theorem
/// stating that an attacker only knows publishable value.
///
/// This is a crucial theorem for confidentiality proofs:
/// if the attacker knows a secret bytestring,
/// we deduce that the bytestring is publishable (attacker knowledge theorem),
/// meaning that its label flows to public (by definition of publishability),
/// which in turn will imply that some set of principals have been compromised (property of labels).

/// We define the attacker knowledge as the weakest predicate on bytes `A`
/// that obeys the following rules:
/// - if b was sent on the network, then A(b)
/// - if b is a compromised state, then A(b)
/// - if forall i. A(b_i) then A(f(b_1, ..., b_n))
///   (for every cryptographic function `f`)
/// We encode these rules in `attacker_rules` below.
/// The attacker rules are parametrized by a (tentative) attacker knowledge predicate,
/// and tells what additional bytestrings the attacker must also know
/// by applying one of the rules.

val attacker_rules:
  trace -> (bytes -> prop) -> bytes ->
  prop
let attacker_rules tr pre msg =
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
  ) \/
  // Concatenation
  (
    exists b1 b2.
      msg == concat b1 b2 /\
      for_allP pre [b1; b2]
  ) \/ (
    exists i b2 buf.
      Some (msg, b2) == split buf i /\
      for_allP pre [buf]
  ) \/ (
    exists i b1 buf.
      Some (b1, msg) == split buf i /\
      for_allP pre [buf]
  ) \/
  // AEAD
  (
    exists key nonce buf ad.
      msg == aead_enc key nonce buf ad /\
      for_allP pre [key; nonce; buf; ad]
  ) \/ (
    exists key nonce buf ad.
      Some msg == aead_dec key nonce buf ad /\
      for_allP pre [key; nonce; buf; ad]
  ) \/
  // Public-key encryption
  (
    exists sk.
      msg == pk sk /\
      for_allP pre [sk]
  ) \/ (
    exists pk nonce buf.
      msg == pke_enc pk nonce buf /\
      for_allP pre [pk; nonce; buf]
  ) \/ (
    exists sk buf.
      Some msg == pke_dec sk buf /\
      for_allP pre [sk; buf]
  ) \/
  // Signature
  (
    exists sk.
      msg == vk sk /\
      for_allP pre [sk]
  ) \/ (
    exists sk nonce buf.
      msg == sign sk nonce buf /\
      for_allP pre [sk; nonce; buf]
  ) \/
  // Hash
  (
    exists buf.
      msg == hash buf /\
      for_allP pre [buf]
  ) \/
  // Diffie-Hellman
  (
    exists sk.
      msg == dh_pk sk /\
      for_allP pre [sk]
  ) \/ (
    exists sk pk.
      msg == dh sk pk /\
      for_allP pre [sk; pk]
  ) \/
  // KDF
  (
    exists salt ikm.
      msg == kdf_extract salt ikm /\
      for_allP pre [salt; ikm]
  ) \/ (
    exists prk info len.
      msg == kdf_expand prk info len /\
      for_allP pre [prk; info]
  ) \/ (
    exists prk info len1 len2.
      len1 <= len2 /\
      msg == kdf_expand prk info len1 /\
      for_allP pre [kdf_expand prk info len2]
  ) \/
  // KEM
  (
    exists sk.
      msg == kem_pk sk /\
      for_allP pre [sk]
  ) \/ (
    exists pk nonce rhs.
      (msg, rhs) == kem_encap pk nonce /\
      for_allP pre [pk; nonce]
  ) \/ (
    exists pk nonce lhs.
      (lhs, msg) == kem_encap pk nonce /\
      for_allP pre [pk; nonce]
  ) \/ (
    exists sk encap.
      Some msg == kem_decap sk encap /\
      for_allP pre [sk; encap]
  ) \/
  // MAC
  (
    exists key buf.
      msg == mac_compute key buf /\
      for_allP pre [key; buf]
  )

/// We now define the attacker knowldege
/// as the weakest predicate such that
/// forall b. attacker_rules A b ==> A b
/// (omitting the trace for simplicity).

[@@ "opaque_to_smt"]
val attacker_knows: trace -> bytes -> prop
let attacker_knows tr =
  mk_weakest_fixpoint (attacker_rules tr)

/// Before proving that the attacker knowledge obeys the attacker rules
/// (i.e. forall b. attacker_rules attacker_knows b ==> attacker_knows b)
/// we need to prove that the tatacker rules is Scott-continuous.

#push-options "--fuel 1 --ifuel 1"
val scott_continuous_for_allP_lemma:
  chain:directed_chain_t bytes ->
  l:list bytes ->
  Lemma
  (requires for_allP (union_set chain.sets) l)
  (ensures exists n. for_allP (chain.sets n) l)
let rec scott_continuous_for_allP_lemma chain l =
  match l with
  | [] -> assert(for_allP (chain.sets 0) l)
  | h::t -> (
    scott_continuous_for_allP_lemma chain t;
    eliminate exists n1 n2. chain.sets n1 h /\ for_allP (chain.sets n2) t
    returns exists n. for_allP (chain.sets n) l
    with _. (
      let n = if n1 <= n2 then n2 else n1 in
      chain.sets_monotonic n1 n;
      chain.sets_monotonic n2 n;
      for_allP_eq (chain.sets n2) t;
      for_allP_eq (chain.sets n) t;
      assert(for_allP (chain.sets n) l)
    )
  )
#pop-options

#push-options "--z3rlimit 25"
val attacker_rules_properties: tr:trace -> f_properties (attacker_rules tr)
let attacker_rules_properties tr = {
  is_scott_continuous = (fun chain x ->
    introduce forall (p:prop). p ==> (exists (n:nat). p) with (
      introduce _ ==> _ with _. (
        introduce exists (n:nat). p with 0 and ()
      )
    );
    introduce forall l. for_allP (union_set chain.sets) l <==> (exists n. for_allP (chain.sets n) l) with (
      FStar.Classical.move_requires (scott_continuous_for_allP_lemma chain) l;
      introduce (exists n. for_allP (chain.sets n) l) ==> for_allP (union_set chain.sets) l with _. (
        eliminate exists n. for_allP (chain.sets n) l
        returns _
        with _. (
          for_allP_eq (chain.sets n) l;
          for_allP_eq (union_set chain.sets) l
        )
      )
    );
    assert((attacker_rules tr (union_set chain.sets) x <==> (exists n. attacker_rules tr (chain.sets n) x)))
  );
  is_monotonic = (fun set1 set2 ->
    introduce forall l. for_allP set1 l ==> for_allP set2 l with (
      for_allP_eq set1 l;
      for_allP_eq set2 l
    )
  );
}
#pop-options

/// As advertised above,
/// we can now prove that the attacker knowledge predicate
/// obeys the attacker rules.

val attacker_knows_obeys_attacker_rules:
  tr:trace -> msg:bytes ->
  Lemma
  (requires attacker_rules tr (attacker_knows tr) msg)
  (ensures attacker_knows tr msg)
let attacker_knows_obeys_attacker_rules tr msg =
  reveal_opaque (`%attacker_knows) (attacker_knows);
  mk_weakest_fixpoint_is_fixpoint (attacker_rules tr) (attacker_rules_properties tr)

/// We prove that the publishability predicate
/// also obeys the attacker rules.

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
  is_corrupt_state_pred_label tr (principal_state_content_label_input prin sess_id content)

#push-options "--ifuel 1 --z3rlimit 25"
val is_publishable_obeys_attacker_rules:
  {|protocol_invariants|} ->
  tr:trace -> msg:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_rules tr (is_publishable tr) msg
  )
  (ensures is_publishable tr msg)
let is_publishable_obeys_attacker_rules #invs tr msg =
  introduce forall l. for_allP (is_publishable tr) l <==> norm [delta_only [`%for_allP]; iota; zeta] (for_allP (is_publishable tr) l) with (
    norm_spec [delta_only [`%for_allP]; iota; zeta] (for_allP (is_publishable tr) l)
  );
  FStar.Classical.forall_intro   (FStar.Classical.move_requires   (msg_sent_on_network_are_publishable tr));
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 (corrupted_state_is_publishable tr));
  FStar.Classical.forall_intro   (FStar.Classical.move_requires   (literal_to_bytes_is_publishable tr));
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
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mac_compute_preserves_publishability tr));
  ()
#pop-options

/// In a trace that satisfy the trace invariant,
/// every bytestring known by the attacker is publishable.
/// We prove this because the publishability predicate obeys the attacker rules,
/// and the attacker knowledge predicate is the weakest predicate
/// that obeys the attacker rules.

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
  FStar.Classical.forall_intro (FStar.Classical.move_requires (is_publishable_obeys_attacker_rules tr));
  mk_weakest_fixpoint_is_weakest (attacker_rules tr) (attacker_rules_properties tr) (is_publishable tr)
