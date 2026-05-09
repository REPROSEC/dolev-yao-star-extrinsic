module DY.Example.AndrewRPC.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.AndrewRPC.Protocol.Total
open DY.Example.AndrewRPC.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

instance crypto_usages_andrew_rpc : crypto_usages = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_andrew_rpc: crypto_predicates
let crypto_predicates_andrew_rpc = {
  default_crypto_predicates with

  aead_pred = {
    pred = (fun tr key_usage key nonce msg ad ->
      match key_usage with
      | AeadKey tag data -> (
        if tag = andrew_rpc_kab_tag then (
          match parse andrew_rpc_key_data data with
          | Some {akd_alice = alice; akd_bob = bob} -> (
            match parse message msg with
            | Some (Msg2 msg2) -> (
              msg2.m2_bob == bob /\
              event_triggered tr bob (Respond1 alice bob msg2.m2_n_a msg2.m2_k_prime_ab) /\
              msg2.m2_k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = msg2.m2_n_a}))
            )
            | _ -> False
          )
          | _ -> False
        ) else if tag = andrew_rpc_k_prime_ab_tag then (
          match parse andrew_rpc_session_key_data data with
          | Some {askd_alice = alice; askd_bob = bob; askd_n_a = n_a} -> (
            match parse message msg with
            | Some (Msg3 msg3) -> (
              msg3.m3_n_a == n_a /\
              event_triggered tr alice (Initiate2 alice bob n_a)
            )
            | _ -> False
          )
          | _ -> False
        ) else False
      )
      | _ -> False
    );
    pred_later = (fun tr1 tr2 key_usage key nonce msg ad ->
      parse_wf_lemma message (bytes_well_formed tr1) msg
    );
  };
}
#pop-options

instance crypto_invariants_andrew_rpc : crypto_invariants = {
  usages = crypto_usages_andrew_rpc;
  preds = crypto_predicates_andrew_rpc;
}

(*** Proofs ***)

#push-options "--z3rlimit 25"
val compute_message1_proof:
  tr:trace ->
  alice:principal -> n_a:bytes ->
  Lemma
  (requires
    is_publishable tr n_a
  )
  (ensures is_publishable tr (compute_message1 alice n_a))
let compute_message1_proof tr alice n_a =
  reveal_opaque (`%compute_message1) (compute_message1 alice n_a);
  let msg = Msg1 alice n_a in
  serialize_wf_lemma message (is_publishable tr) msg
#pop-options

#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message1_proof:
  tr:trace ->
  msg_bytes:bytes ->
  Lemma
  (requires
    is_publishable tr msg_bytes
  )
  (ensures (
    match decode_message1 msg_bytes with
    | None -> True
    | Some (alice, n_a) -> (
      is_publishable tr n_a
    )
  ))
let decode_message1_proof tr msg_bytes =
  reveal_opaque (`%decode_message1) (decode_message1 msg_bytes);
  match decode_message1 msg_bytes with
  | None -> ()
  | Some (alice, n_a) ->
    parse_wf_lemma message (is_publishable tr) msg_bytes
#pop-options

#push-options "--z3rlimit 50"
val compute_message2_proof:
  tr:trace ->
  alice:principal -> bob:principal -> kab:bytes -> n_a:bytes -> k_prime_ab:bytes -> nonce:bytes ->
  Lemma
  (requires
    kab `has_usage tr` (AeadKey andrew_rpc_kab_tag (serialize _ {akd_alice = alice; akd_bob = bob})) /\
    is_secret (andrew_rpc_nonce_label alice bob) tr kab /\
    is_publishable tr n_a /\
    is_knowable_by (andrew_rpc_nonce_label alice bob) tr k_prime_ab /\
    k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = n_a})) /\
    is_publishable tr nonce /\
    event_triggered tr bob (Respond1 alice bob n_a k_prime_ab)
  )
  (ensures is_publishable tr (compute_message2 kab n_a k_prime_ab nonce bob))
let compute_message2_proof tr alice bob kab n_a k_prime_ab nonce =
  reveal_opaque (`%compute_message2) (compute_message2 kab n_a k_prime_ab nonce bob);
  let msg2_struct = {m2_n_a = n_a; m2_k_prime_ab = k_prime_ab; m2_bob = bob} in
  let msg = Msg2 msg2_struct in
  // The plaintext serialized message is knowable by kab's label
  serialize_wf_lemma message (is_knowable_by (andrew_rpc_nonce_label alice bob) tr) msg;
  let plain_bytes = serialize message msg in
  // Show we are in the AEAD-pred branch (kab honest with the right tag)
  let key_usg = AeadKey andrew_rpc_kab_tag (serialize _ {akd_alice = alice; akd_bob = bob}) in
  // The serialize/parse round-trip on the key data
  parse_serialize_inv_lemma #bytes andrew_rpc_key_data ({akd_alice = alice; akd_bob = bob});
  // The serialize/parse round-trip on the message
  parse_serialize_inv_lemma #bytes message msg;
  // Encryption result is publishable (label is public always); bytes_invariant follows from aead_pred
  let ciphertext = aead_enc kab nonce plain_bytes empty in
  assert(get_label tr ciphertext == public);
  ()
#pop-options

#push-options "--ifuel 1 --fuel 0 --z3rlimit 50"
val decode_message2_proof:
  tr:trace ->
  alice:principal -> bob:principal -> kab:bytes -> msg2_with_nonce:bytes ->
  Lemma
  (requires
    kab `has_usage tr` (AeadKey andrew_rpc_kab_tag (serialize _ {akd_alice = alice; akd_bob = bob})) /\
    is_secret (andrew_rpc_nonce_label alice bob) tr kab /\
    is_publishable tr msg2_with_nonce
  )
  (ensures (
    match decode_message2 kab msg2_with_nonce with
    | None -> True
    | Some msg2 -> (
      is_knowable_by (andrew_rpc_nonce_label alice bob) tr msg2.m2_k_prime_ab /\ (
        (is_corrupt tr (andrew_rpc_nonce_label alice bob)) \/ (
          msg2.m2_bob == bob /\
          event_triggered tr bob (Respond1 alice bob msg2.m2_n_a msg2.m2_k_prime_ab) /\
          msg2.m2_k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = msg2.m2_n_a}))
        )
      )
    )
  ))
let decode_message2_proof tr alice bob kab msg2_with_nonce =
  reveal_opaque (`%decode_message2) (decode_message2 kab msg2_with_nonce);
  match decode_message2 kab msg2_with_nonce with
  | None -> ()
  | Some msg2 ->
    let Some (nonce, ciphertext) = split msg2_with_nonce 12 in
    let ad = empty in
    let Some msg_bytes = aead_dec kab nonce ciphertext ad in
    parse_serialize_inv_lemma #bytes andrew_rpc_key_data ({akd_alice = alice; akd_bob = bob});
    parse_wf_lemma message (is_knowable_by (andrew_rpc_nonce_label alice bob) tr) msg_bytes;
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg_bytes;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg_bytes
#pop-options

#push-options "--z3rlimit 50 --ifuel 1"
val compute_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal -> n_a:bytes -> k_prime_ab:bytes -> nonce:bytes ->
  Lemma
  (requires
    bytes_invariant tr k_prime_ab /\
    is_publishable tr nonce /\
    is_publishable tr n_a /\
    (
      is_publishable tr k_prime_ab \/
      (
        k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = n_a})) /\
        event_triggered tr alice (Initiate2 alice bob n_a)
      )
    )
  )
  (ensures is_publishable tr (compute_message3 k_prime_ab n_a nonce))
let compute_message3_proof tr alice bob n_a k_prime_ab nonce =
  reveal_opaque (`%compute_message3) (compute_message3 k_prime_ab n_a nonce);
  let msg3_struct = {m3_n_a = n_a} in
  let msg = Msg3 msg3_struct in
  serialize_wf_lemma message (is_publishable tr) msg;
  let plain_bytes = serialize message msg in
  parse_serialize_inv_lemma #bytes andrew_rpc_session_key_data ({askd_alice = alice; askd_bob = bob; askd_n_a = n_a});
  parse_serialize_inv_lemma #bytes message msg;
  FStar.Classical.move_requires (aead_enc_preserves_publishability tr k_prime_ab nonce plain_bytes) empty;
  let ciphertext = aead_enc k_prime_ab nonce plain_bytes empty in
  assert(get_label tr ciphertext == public)
#pop-options

#push-options "--ifuel 1 --fuel 0 --z3rlimit 50"
val decode_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal -> n_a:bytes -> k_prime_ab:bytes -> msg3_with_nonce:bytes ->
  Lemma
  (requires
    k_prime_ab `has_usage tr` (AeadKey andrew_rpc_k_prime_ab_tag (serialize _ {askd_alice = alice; askd_bob = bob; askd_n_a = n_a})) /\
    is_secret (andrew_rpc_session_key_label alice bob n_a) tr k_prime_ab /\
    is_publishable tr msg3_with_nonce
  )
  (ensures (
    match decode_message3 k_prime_ab msg3_with_nonce with
    | None -> True
    | Some msg3 -> (
      (is_corrupt tr (andrew_rpc_session_key_label alice bob n_a)) \/ (
        msg3.m3_n_a == n_a /\
        event_triggered tr alice (Initiate2 alice bob n_a)
      )
    )
  ))
let decode_message3_proof tr alice bob n_a k_prime_ab msg3_with_nonce =
  reveal_opaque (`%decode_message3) (decode_message3 k_prime_ab msg3_with_nonce);
  match decode_message3 k_prime_ab msg3_with_nonce with
  | None -> ()
  | Some msg3 ->
    let Some (nonce, ciphertext) = split msg3_with_nonce 12 in
    let ad = empty in
    let Some msg_bytes = aead_dec k_prime_ab nonce ciphertext ad in
    parse_serialize_inv_lemma #bytes andrew_rpc_session_key_data ({askd_alice = alice; askd_bob = bob; askd_n_a = n_a});
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg_bytes;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg_bytes
#pop-options

#push-options "--z3rlimit 25"
val compute_message4_proof:
  tr:trace ->
  n_b:bytes ->
  Lemma
  (requires
    is_publishable tr n_b
  )
  (ensures is_publishable tr (compute_message4 n_b))
let compute_message4_proof tr n_b =
  reveal_opaque (`%compute_message4) (compute_message4 n_b);
  let msg = Msg4 n_b in
  serialize_wf_lemma message (is_publishable tr) msg
#pop-options

#push-options "--ifuel 1 --fuel 0 --z3rlimit 25"
val decode_message4_proof:
  tr:trace ->
  msg_bytes:bytes ->
  Lemma
  (requires
    is_publishable tr msg_bytes
  )
  (ensures (
    match decode_message4 msg_bytes with
    | None -> True
    | Some n_b -> (
      is_publishable tr n_b
    )
  ))
let decode_message4_proof tr msg_bytes =
  reveal_opaque (`%decode_message4) (decode_message4 msg_bytes);
  match decode_message4 msg_bytes with
  | None -> ()
  | Some n_b ->
    parse_wf_lemma message (is_publishable tr) msg_bytes
#pop-options
