module DY.Example.CCITT.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.CCITT.Protocol.Total
open DY.Example.CCITT.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

instance crypto_usages_ccitt : crypto_usages = default_crypto_usages

#push-options "--ifuel 2 --fuel 1"
val crypto_predicates_ccitt: crypto_predicates
let crypto_predicates_ccitt = {
  default_crypto_predicates with

  pke_pred = {
    pred = (fun tr sk_usage pk msg ->
      match sk_usage with
      | PkeKey tag data ->
        if tag = ccitt_pke_tag then (
          match parse long_term_key_usage_data data with
          | Some {who = bob} -> (
            match parse inner_payload msg with
            | Some ip ->
              exists alice ta na xa.
                event_triggered tr alice (AliceSends alice bob ta na xa ip.ya) /\
                (get_label tr ip.ya) `can_flow tr` (ccitt_label alice bob)
            | None -> False
          )
          | None -> False
        ) else False
      | _ -> False
    );
    pred_later = (fun tr1 tr2 sk_usage pk msg ->
      parse_wf_lemma inner_payload (bytes_well_formed tr1) msg
    );
  };

  sign_pred = {
    pred = (fun tr sk_usage vk msg ->
      match sk_usage with
      | SigKey tag data ->
        if tag = ccitt_sign_tag then (
          match parse long_term_key_usage_data data with
          | Some {who = alice} -> (
            match parse sig_message msg with
            | Some (SigInner h_ya) ->
              // Inner signature variant: hash_of_ya == hash ya for some ya, and an
              // AliceSends event was triggered for that ya.
              exists ya. h_ya == hash ya /\
                (exists bob ta na xa. event_triggered tr alice (AliceSends alice bob ta na xa ya))
            | Some (SigOuter payload) ->
              // Outer signature variant: inner_cipher commits to a specific ya via
              // symbolic injectivity of pke_enc, tying the outer-signed event to that ya.
              exists ya pk_b' inner_nonce' inner_sig'.
                payload.inner_cipher == pke_enc pk_b' inner_nonce' (serialize inner_payload ({ya; sig_h_ya = inner_sig'} <: inner_payload)) /\
                event_triggered tr alice (AliceSends alice payload.bob payload.ta payload.na payload.xa ya)
            | None -> False
          )
          | None -> False
        ) else False
      | _ -> False
    );
    pred_later = (fun tr1 tr2 sk_usage vk msg ->
      parse_wf_lemma sig_message (bytes_well_formed tr1) msg
    );
  };
}
#pop-options

instance crypto_invariants_ccitt : crypto_invariants = {
  usages = crypto_usages_ccitt;
  preds = crypto_predicates_ccitt;
}

(*** Proofs ***)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 2 --split_queries always"
val compute_message1_proof:
  tr:trace ->
  ta:bytes -> na:bytes -> bob:principal -> xa:bytes -> ya:bytes ->
  pk_b:bytes -> sk_a:bytes ->
  n_inner_sig:bytes -> n_inner_pke:bytes -> n_outer:bytes ->
  alice:principal ->
  Lemma
  (requires
    is_publishable tr ta /\
    is_publishable tr na /\
    is_publishable tr xa /\
    is_knowable_by (ccitt_label alice bob) tr ya /\
    is_public_key_for tr pk_b (LongTermPkeKey ccitt_pke_tag) bob /\
    is_private_key_for tr sk_a (LongTermSigKey ccitt_sign_tag) alice /\
    is_secret (long_term_key_label alice) tr n_inner_sig /\
    n_inner_sig `has_usage tr` SigNonce /\
    is_secret (long_term_key_label alice) tr n_inner_pke /\
    n_inner_pke `has_usage tr` PkeNonce /\
    is_secret (long_term_key_label alice) tr n_outer /\
    n_outer `has_usage tr` SigNonce /\
    event_triggered tr alice (AliceSends alice bob ta na xa ya)
  )
  (ensures is_publishable tr (compute_message1 ta na bob xa ya pk_b sk_a n_inner_sig n_inner_pke n_outer))
let compute_message1_proof tr ta na bob xa ya pk_b sk_a n_inner_sig n_inner_pke n_outer alice =
  reveal_opaque (`%compute_message1) (compute_message1 ta na bob xa ya pk_b sk_a n_inner_sig n_inner_pke n_outer);
  let h_ya = hash ya in
  let inner_sig_msg : sig_message = SigInner h_ya in
  let inner_sig_msg_bytes = serialize sig_message inner_sig_msg in
  let sig_h_ya = sign sk_a n_inner_sig inner_sig_msg_bytes in
  let ip = ({ ya; sig_h_ya } <: inner_payload) in
  let sk_usg = long_term_key_type_to_usage (LongTermSigKey ccitt_sign_tag) alice in
  let pk_usg = long_term_key_type_to_usage (LongTermPkeKey ccitt_pke_tag) bob in
  parse_serialize_inv_lemma #bytes long_term_key_usage_data ({who = alice});
  parse_serialize_inv_lemma #bytes sig_message inner_sig_msg;
  // --- Inner sign: derive bytes_invariant tr sig_h_ya via SigInner branch of sign_pred
  serialize_wf_lemma sig_message (is_knowable_by (ccitt_label alice bob) tr) inner_sig_msg;
  assert(sign_pred.pred tr sk_usg (vk sk_a) inner_sig_msg_bytes);
  bytes_invariant_sign tr sk_a sk_usg n_inner_sig inner_sig_msg_bytes;
  assert(bytes_invariant tr sig_h_ya);
  assert(get_label tr sig_h_ya == get_label tr inner_sig_msg_bytes);
  assert(is_knowable_by (ccitt_label alice bob) tr sig_h_ya);
  // --- Inner payload bytes
  parse_serialize_inv_lemma #bytes inner_payload ip;
  serialize_wf_lemma inner_payload (is_knowable_by (ccitt_label alice bob) tr) ip;
  let ip_bytes = serialize inner_payload ip in
  // --- Inner pke: derive bytes_invariant tr inner_cipher
  assert(parse inner_payload ip_bytes == Some ip);
  assert(ip.ya == ya);
  introduce exists alice' ta' na' xa'. event_triggered tr alice' (AliceSends alice' bob ta' na' xa' ip.ya) /\
    (get_label tr ip.ya) `can_flow tr` (ccitt_label alice' bob)
  with alice ta na xa and ();
  assert(pke_pred.pred tr pk_usg pk_b ip_bytes);
  bytes_invariant_pke_enc tr pk_b pk_usg n_inner_pke ip_bytes;
  let inner_cipher = pke_enc pk_b n_inner_pke ip_bytes in
  assert(bytes_invariant tr inner_cipher);
  assert(is_publishable tr inner_cipher);
  // --- Outer payload bytes
  let payload = ({ ta; na; bob; xa; inner_cipher } <: msg1_payload) in
  parse_serialize_inv_lemma #bytes msg1_payload payload;
  let outer_sig_msg : sig_message = SigOuter payload in
  let outer_sig_msg_bytes = serialize sig_message outer_sig_msg in
  parse_serialize_inv_lemma #bytes sig_message outer_sig_msg;
  serialize_wf_lemma sig_message (is_publishable tr) outer_sig_msg;
  // --- Outer sign: derive bytes_invariant tr signature via SigOuter branch of sign_pred
  assert(payload.inner_cipher == pke_enc pk_b n_inner_pke (serialize inner_payload ({ya; sig_h_ya} <: inner_payload)));
  assert(sign_pred.pred tr sk_usg (vk sk_a) outer_sig_msg_bytes);
  bytes_invariant_sign tr sk_a sk_usg n_outer outer_sig_msg_bytes;
  let signature = sign sk_a n_outer outer_sig_msg_bytes in
  serialize_wf_lemma msg1_payload (is_publishable tr) payload;
  assert(bytes_invariant tr signature);
  assert(is_publishable tr signature);
  // --- Final message
  let final_msg : message = Msg1 payload signature in
  serialize_wf_lemma message (is_publishable tr) final_msg
#pop-options

#push-options "--z3rlimit 2000 --fuel 2 --ifuel 4"
val decode_message1_event_helper:
  tr:trace ->
  alice:principal -> bob:principal ->
  payload:msg1_payload -> signature:bytes ->
  sk_b:bytes -> vk_a:bytes -> ip_bytes:bytes -> ip:inner_payload ->
  Lemma
  (requires
    is_private_key_for tr sk_b (LongTermPkeKey ccitt_pke_tag) bob /\
    is_public_key_for tr vk_a (LongTermSigKey ccitt_sign_tag) alice /\
    bytes_invariant tr (serialize sig_message (SigOuter payload)) /\
    bytes_invariant tr signature /\
    verify vk_a (serialize sig_message (SigOuter payload)) signature /\
    pke_dec sk_b payload.inner_cipher == Some ip_bytes /\
    parse inner_payload ip_bytes == Some ip /\
    payload.bob == bob
  )
  (ensures
    is_corrupt tr (ccitt_label alice bob) \/
    event_triggered tr alice (AliceSends alice bob payload.ta payload.na payload.xa ip.ya)
  )
let decode_message1_event_helper tr alice bob payload signature sk_b vk_a ip_bytes ip =
  reveal_opaque (`%pke_dec) (pke_dec sk_b);
  reveal_opaque (`%pke_enc) (pke_enc);
  parse_serialize_inv_lemma #bytes inner_payload ip;
  parse_serialize_inv_lemma #bytes long_term_key_usage_data ({who = alice});
  let outer_sig_msg : sig_message = SigOuter payload in
  let outer_sig_msg_bytes = serialize sig_message outer_sig_msg in
  parse_serialize_inv_lemma #bytes sig_message outer_sig_msg;
  let sk_usg_a = long_term_key_type_to_usage (LongTermSigKey ccitt_sign_tag) alice in
  bytes_invariant_verify tr vk_a sk_usg_a outer_sig_msg_bytes signature;
  // bytes_invariant_verify gives:
  //   sign_pred.pred tr sk_usg_a vk_a outer_sig_msg_bytes  \/  get_signkey_label vk_a `can_flow tr` public
  // get_signkey_label vk_a == long_term_key_label alice.
  // Show that the right disjunct (signkey corrupt) implies ccitt_label corrupt.
  introduce
    (get_signkey_label tr vk_a) `can_flow tr` public ==>
    is_corrupt tr (ccitt_label alice bob)
  with _. (
    // get_signkey_label vk_a == long_term_key_label alice (from is_public_key_for).
    assert(get_signkey_label tr vk_a == long_term_key_label alice);
    assert(is_corrupt tr (long_term_key_label alice));
    // principal_label alice can_flow long_term_key_label alice. SMT pat triggers via
    // state_pred_label_can_flow_state_pred_label when both labels are unfolded.
    assert(principal_label alice `can_flow tr` long_term_key_label alice);
    assert(is_corrupt tr (principal_label alice));
    assert(is_corrupt tr (ccitt_label alice bob))
  );
  introduce
    sign_pred.pred tr sk_usg_a vk_a outer_sig_msg_bytes ==>
    event_triggered tr alice (AliceSends alice bob payload.ta payload.na payload.xa ip.ya)
  with _. (
    eliminate exists ya' pk_b' inner_nonce' inner_sig'.
      payload.inner_cipher == pke_enc pk_b' inner_nonce' (serialize inner_payload ({ya = ya'; sig_h_ya = inner_sig'} <: inner_payload)) /\
      event_triggered tr alice (AliceSends alice payload.bob payload.ta payload.na payload.xa ya')
    returns event_triggered tr alice (AliceSends alice bob payload.ta payload.na payload.xa ip.ya)
    with _. (
      let ip' : inner_payload = {ya = ya'; sig_h_ya = inner_sig'} in
      parse_serialize_inv_lemma #bytes inner_payload ip';
      assert(ip.ya == ya')
    )
  )
#pop-options

#push-options "--z3rlimit 1000 --fuel 4 --ifuel 4"
val decode_message1_proof:
  tr:trace ->
  bob:principal -> msg_bytes:bytes ->
  sk_b:bytes -> vk_a:bytes -> alice:principal ->
  Lemma
  (requires
    is_private_key_for tr sk_b (LongTermPkeKey ccitt_pke_tag) bob /\
    is_public_key_for tr vk_a (LongTermSigKey ccitt_sign_tag) alice /\
    is_publishable tr msg_bytes
  )
  (ensures (
    match decode_message1 bob msg_bytes sk_b vk_a with
    | Some (ta, na, bob', xa, ya) ->
      is_publishable tr ta /\
      is_publishable tr na /\
      bob' == bob /\
      is_publishable tr xa /\
      is_knowable_by (long_term_key_label bob) tr ya /\
      (is_corrupt tr (ccitt_label alice bob) \/
       event_triggered tr alice (AliceSends alice bob ta na xa ya))
    | None -> True
  ))
let decode_message1_proof tr bob msg_bytes sk_b vk_a alice =
  reveal_opaque (`%decode_message1) (decode_message1 bob msg_bytes sk_b vk_a);
  parse_wf_lemma message (is_publishable tr) msg_bytes;
  match decode_message1 bob msg_bytes sk_b vk_a with
  | None -> ()
  | Some (ta, na, bob', xa, ya) -> (
    let Some msg = parse message msg_bytes in
    let Msg1 payload signature = msg in
    serialize_wf_lemma msg1_payload (is_publishable tr) payload;
    let outer_sig_msg : sig_message = SigOuter payload in
    serialize_wf_lemma sig_message (is_publishable tr) outer_sig_msg;
    let pk_usg = long_term_key_type_to_usage (LongTermPkeKey ccitt_pke_tag) bob in
    let Some ip_bytes = pke_dec sk_b payload.inner_cipher in
    bytes_invariant_pke_dec tr sk_b pk_usg payload.inner_cipher;
    parse_wf_lemma inner_payload (is_knowable_by (long_term_key_label bob) tr) ip_bytes;
    let Some ip = parse inner_payload ip_bytes in
    decode_message1_event_helper tr alice bob payload signature sk_b vk_a ip_bytes ip
  )
#pop-options
