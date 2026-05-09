module DY.Example.CCITT.Debug.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.CCITT.Protocol.Total
open DY.Example.CCITT.Protocol.Total.Proof
open DY.Example.CCITT.Protocol.Stateful
open DY.Example.CCITT.Protocol.Stateful.Proof
open DY.Example.CCITT.Debug

#set-options "--fuel 1 --ifuel 2 --z3rlimit 1200 --z3cliopt 'smt.qi.eager_threshold=100' --split_queries always"

val debug_proof:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_private_keys_invariant
  )
  (ensures (
    let (_, tr_out) = debug () tr in
    trace_invariant tr_out
  ))
let debug_proof tr =
  let alice = "alice" in
  let bob = "bob" in
  let (alice_priv_key_id, tr_a) = initialize_private_keys alice tr in
  let (_, tr_b) = generate_private_key alice alice_priv_key_id (LongTermSigKey ccitt_sign_tag) tr_a in
  let (alice_pki_id, tr_c) = initialize_pki alice tr_b in
  let (bob_priv_key_id, tr_d) = initialize_private_keys bob tr_c in
  let (_, tr_e) = generate_private_key bob bob_priv_key_id (LongTermPkeKey ccitt_pke_tag) tr_d in
  let (bob_pki_id, tr_f) = initialize_pki bob tr_e in
  match compute_public_key alice alice_priv_key_id (LongTermSigKey ccitt_sign_tag) tr_f with
  | (None, _) -> ()
  | (Some vk_a, tr_g) -> (
    let (_, tr_h) = install_public_key bob bob_pki_id (LongTermSigKey ccitt_sign_tag) alice vk_a tr_g in
    match compute_public_key bob bob_priv_key_id (LongTermPkeKey ccitt_pke_tag) tr_h with
    | (None, _) -> ()
    | (Some pk_b, tr_i) -> (
      let (_, tr_j) = install_public_key alice alice_pki_id (LongTermPkeKey ccitt_pke_tag) bob pk_b tr_i in
      let ta = serialize string "2026-05-09" in
      let xa = serialize string "public data" in
      let ya = serialize string "secret data" in
      serialize_wf_lemma string (is_publishable tr_j) "2026-05-09";
      serialize_wf_lemma string (is_publishable tr_j) "public data";
      serialize_wf_lemma string (is_publishable tr_j) "secret data";
      assert(is_publishable tr_j ta);
      assert(is_publishable tr_j xa);
      assert(is_publishable tr_j ya);
      assert(is_knowable_by (ccitt_label alice bob) tr_j ya);
      alice_send_msg1_proof alice_pki_id alice_priv_key_id alice bob ta xa ya tr_j;
      match alice_send_msg1 alice_pki_id alice_priv_key_id alice bob ta xa ya tr_j with
      | (None, _) -> ()
      | (Some msg1_id, tr_k) -> (
        bob_receive_msg1_proof bob_pki_id bob_priv_key_id bob alice msg1_id tr_k
      )
    )
  )
