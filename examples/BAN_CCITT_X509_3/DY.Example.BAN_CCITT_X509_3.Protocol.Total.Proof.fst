module DY.Example.BAN_CCITT_X509_3.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.BAN_CCITT_X509_3.Protocol.Total
open DY.Example.BAN_CCITT_X509_3.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

instance ban_ccitt_crypto_usages: crypto_usages = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
val ban_ccitt_crypto_preds: crypto_predicates
let ban_ccitt_crypto_preds = {
  default_crypto_predicates with

  pke_pred = {
    pred = (fun tr sk_usage pk msg ->
      (exists prin. sk_usage == long_term_key_type_to_usage (LongTermPkeKey "BAN_CCITT.PkeKey") prin /\ (
        match parse userdata msg with
        | Some ud -> (
          (exists alice n_a x_a y_a. ud.data == y_a /\ event_triggered tr alice (Initiate1 alice prin n_a x_a y_a)) \/
          (exists bob n_b x_b y_b n_a. ud.data == y_b /\ event_triggered tr bob (Respond1 bob prin n_b x_b y_b n_a))
        )
        | None -> False
      ))
    );
    pred_later = (fun tr1 tr2 sk_usage pk msg ->
      parse_wf_lemma userdata (bytes_well_formed tr1) msg
    );
  };

  sign_pred = {
    pred = (fun tr sk_usage vk msg ->
      (exists prin. sk_usage == long_term_key_type_to_usage (LongTermSigKey "BAN_CCITT.SigKey") prin /\ (
        match parse sig_message msg with
        | Some (SigMsg1 sm1) ->
          exists y_a. event_triggered tr prin (Initiate1 prin sm1.sm1_bob sm1.sm1_n_a sm1.sm1_x_a y_a)
        | Some (SigMsg2 sm2) ->
          exists y_b. event_triggered tr prin (Respond1 prin sm2.sm2_alice sm2.sm2_n_b sm2.sm2_x_b y_b sm2.sm2_n_a)
        | Some (SigMsg3 sm3) ->
          event_triggered tr prin (Initiate2 prin sm3.sm3_bob sm3.sm3_n_b)
        | None -> False
      ))
    );
    pred_later = (fun tr1 tr2 sk_usage vk msg ->
      parse_wf_lemma sig_message (bytes_well_formed tr1) msg
    );
  };
}
#pop-options

instance ban_ccitt_crypto_invs: crypto_invariants = {
  usages = ban_ccitt_crypto_usages;
  preds = ban_ccitt_crypto_preds;
}

(*** Proofs ***)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val compute_message1_proof:
  tr:trace ->
  alice:principal -> bob:principal -> pk_b:bytes -> n_a:bytes -> x_a:bytes -> y_a:bytes -> pke_nonce:bytes -> sig_nonce:bytes -> sk_a:bytes ->
  Lemma
    (requires
      event_triggered tr alice (Initiate1 alice bob n_a x_a y_a) /\
      is_publishable tr x_a /\
      is_publishable tr n_a /\
      is_knowable_by (ban_ccitt_label alice bob) tr y_a /\
      is_private_key_for tr sk_a (LongTermSigKey "BAN_CCITT.SigKey") alice /\
      is_public_key_for tr pk_b (LongTermPkeKey "BAN_CCITT.PkeKey") bob /\
      is_secret (long_term_key_label alice) tr pke_nonce /\ pke_nonce `has_usage tr` PkeNonce /\
      is_secret (long_term_key_label alice) tr sig_nonce /\ sig_nonce `has_usage tr` SigNonce
    )
    (ensures is_publishable tr (compute_message1 alice bob pk_b n_a x_a y_a pke_nonce sig_nonce sk_a))
let compute_message1_proof tr alice bob pk_b n_a x_a y_a pke_nonce sig_nonce sk_a =
  reveal_opaque (`%compute_message1) (compute_message1 alice bob pk_b n_a x_a y_a pke_nonce sig_nonce sk_a);
  let inner_payload : userdata = {data=y_a} in
  serialize_wf_lemma userdata (is_knowable_by (ban_ccitt_label alice bob) tr) inner_payload;
  let y_a_enc = pke_enc pk_b pke_nonce (serialize userdata inner_payload) in
  assert(is_publishable tr y_a_enc);
  let signed_part : sig_message1 = { sm1_n_a = n_a; sm1_bob = bob; sm1_x_a = x_a; sm1_y_a_enc = y_a_enc } in
  let sig_payload : sig_message = SigMsg1 signed_part in
  serialize_wf_lemma sig_message (is_publishable tr) sig_payload;
  let sg = sign sk_a sig_nonce (serialize sig_message sig_payload) in
  parse_serialize_inv_lemma #bytes sig_message sig_payload;
  assert(is_publishable tr sg);
  let m : message = Msg1 { m1_alice = alice; m1_n_a = n_a; m1_bob = bob; m1_x_a = x_a; m1_y_a_enc = y_a_enc; m1_sg = sg } in
  serialize_wf_lemma message (is_publishable tr) m
#pop-options

#push-options "--ifuel 2 --fuel 1 --z3rlimit 100"
val decode_message1_proof:
  tr:trace ->
  msg1_bytes:bytes -> bob:principal -> alice:principal -> vk_a:bytes ->
  Lemma
  (requires
    is_publishable tr msg1_bytes /\
    is_public_key_for tr vk_a (LongTermSigKey "BAN_CCITT.SigKey") alice
  )
  (ensures (
    match decode_message1 msg1_bytes bob vk_a with
    | Some msg1 -> (
      is_publishable tr msg1.m1_n_a /\
      is_publishable tr msg1.m1_x_a /\
      is_publishable tr msg1.m1_y_a_enc /\
      (is_corrupt tr (long_term_key_label alice) \/ (exists y_a. event_triggered tr alice (Initiate1 alice bob msg1.m1_n_a msg1.m1_x_a y_a)))
    )
    | None -> True
  ))
let decode_message1_proof tr msg1_bytes bob alice vk_a =
  reveal_opaque (`%decode_message1) (decode_message1 msg1_bytes bob vk_a);
  match decode_message1 msg1_bytes bob vk_a with
  | None -> ()
  | Some msg1 ->
    parse_wf_lemma message (is_publishable tr) msg1_bytes;
    let signed_part : sig_message1 = { sm1_n_a = msg1.m1_n_a; sm1_bob = msg1.m1_bob; sm1_x_a = msg1.m1_x_a; sm1_y_a_enc = msg1.m1_y_a_enc } in
    let sig_payload : sig_message = SigMsg1 signed_part in
    serialize_wf_lemma sig_message (is_publishable tr) sig_payload;
    parse_serialize_inv_lemma #bytes sig_message sig_payload
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val compute_message2_proof:
  tr:trace ->
  bob:principal -> alice:principal -> pk_a:bytes -> n_b:bytes -> n_a:bytes -> x_b:bytes -> y_b:bytes -> pke_nonce:bytes -> sig_nonce:bytes -> sk_b:bytes ->
  Lemma
    (requires
      event_triggered tr bob (Respond1 bob alice n_b x_b y_b n_a) /\
      is_publishable tr x_b /\ is_publishable tr n_a /\
      is_publishable tr n_b /\
      is_knowable_by (ban_ccitt_label alice bob) tr y_b /\
      is_private_key_for tr sk_b (LongTermSigKey "BAN_CCITT.SigKey") bob /\
      is_public_key_for tr pk_a (LongTermPkeKey "BAN_CCITT.PkeKey") alice /\
      is_secret (long_term_key_label bob) tr pke_nonce /\ pke_nonce `has_usage tr` PkeNonce /\
      is_secret (long_term_key_label bob) tr sig_nonce /\ sig_nonce `has_usage tr` SigNonce
    )
    (ensures is_publishable tr (compute_message2 bob alice pk_a n_b n_a x_b y_b pke_nonce sig_nonce sk_b))
let compute_message2_proof tr bob alice pk_a n_b n_a x_b y_b pke_nonce sig_nonce sk_b =
  reveal_opaque (`%compute_message2) (compute_message2 bob alice pk_a n_b n_a x_b y_b pke_nonce sig_nonce sk_b);
  let inner_payload : userdata = {data=y_b} in
  serialize_wf_lemma userdata (is_knowable_by (ban_ccitt_label alice bob) tr) inner_payload;
  let y_b_enc = pke_enc pk_a pke_nonce (serialize userdata inner_payload) in
  assert(is_publishable tr y_b_enc);
  let signed_part : sig_message2 = { sm2_n_b = n_b; sm2_alice = alice; sm2_n_a = n_a; sm2_x_b = x_b; sm2_y_b_enc = y_b_enc } in
  let sig_payload : sig_message = SigMsg2 signed_part in
  serialize_wf_lemma sig_message (is_publishable tr) sig_payload;
  let sg = sign sk_b sig_nonce (serialize sig_message sig_payload) in
  parse_serialize_inv_lemma #bytes sig_message sig_payload;
  assert(is_publishable tr sg);
  let m : message = Msg2 { m2_bob = bob; m2_n_b = n_b; m2_alice = alice; m2_n_a = n_a; m2_x_b = x_b; m2_y_b_enc = y_b_enc; m2_sg = sg } in
  serialize_wf_lemma message (is_publishable tr) m
#pop-options

#push-options "--ifuel 2 --fuel 1 --z3rlimit 100"
val decode_message2_proof:
  tr:trace ->
  msg2_bytes:bytes -> alice:principal -> bob:principal -> vk_b:bytes -> n_a:bytes ->
  Lemma
  (requires
    is_publishable tr msg2_bytes /\
    is_public_key_for tr vk_b (LongTermSigKey "BAN_CCITT.SigKey") bob
  )
  (ensures (
    match decode_message2 msg2_bytes alice vk_b n_a with
    | Some msg2 -> (
      is_publishable tr msg2.m2_n_b /\
      is_publishable tr msg2.m2_x_b /\
      is_publishable tr msg2.m2_y_b_enc /\
      (is_corrupt tr (long_term_key_label bob) \/ (exists y_b. event_triggered tr bob (Respond1 bob alice msg2.m2_n_b msg2.m2_x_b y_b n_a)))
    )
    | None -> True
  ))
let decode_message2_proof tr msg2_bytes alice bob vk_b n_a =
  reveal_opaque (`%decode_message2) (decode_message2 msg2_bytes alice vk_b n_a);
  match decode_message2 msg2_bytes alice vk_b n_a with
  | None -> ()
  | Some msg2 ->
    parse_wf_lemma message (is_publishable tr) msg2_bytes;
    let signed_part : sig_message2 = { sm2_n_b = msg2.m2_n_b; sm2_alice = msg2.m2_alice; sm2_n_a = msg2.m2_n_a; sm2_x_b = msg2.m2_x_b; sm2_y_b_enc = msg2.m2_y_b_enc } in
    let sig_payload : sig_message = SigMsg2 signed_part in
    serialize_wf_lemma sig_message (is_publishable tr) sig_payload;
    parse_serialize_inv_lemma #bytes sig_message sig_payload
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val compute_message3_proof:
  tr:trace ->
  alice:principal -> bob:principal -> n_b:bytes -> sig_nonce:bytes -> sk_a:bytes ->
  Lemma
    (requires
      event_triggered tr alice (Initiate2 alice bob n_b) /\
      is_publishable tr n_b /\
      is_private_key_for tr sk_a (LongTermSigKey "BAN_CCITT.SigKey") alice /\
      is_secret (long_term_key_label alice) tr sig_nonce /\ sig_nonce `has_usage tr` SigNonce
    )
    (ensures is_publishable tr (compute_message3 alice bob n_b sig_nonce sk_a))
let compute_message3_proof tr alice bob n_b sig_nonce sk_a =
  reveal_opaque (`%compute_message3) (compute_message3 alice bob n_b sig_nonce sk_a);
  let signed_part : sig_message3 = { sm3_bob = bob; sm3_n_b = n_b } in
  let sig_payload : sig_message = SigMsg3 signed_part in
  serialize_wf_lemma sig_message (is_publishable tr) sig_payload;
  let sg = sign sk_a sig_nonce (serialize sig_message sig_payload) in
  parse_serialize_inv_lemma #bytes sig_message sig_payload;
  assert(is_publishable tr sg);
  let m : message = Msg3 { m3_alice = alice; m3_bob = bob; m3_n_b = n_b; m3_sg = sg } in
  serialize_wf_lemma message (is_publishable tr) m
#pop-options

#push-options "--ifuel 2 --fuel 1 --z3rlimit 100"
val decode_message3_proof:
  tr:trace ->
  msg3_bytes:bytes -> bob:principal -> alice:principal -> vk_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    is_publishable tr msg3_bytes /\
    is_public_key_for tr vk_a (LongTermSigKey "BAN_CCITT.SigKey") alice
  )
  (ensures (
    match decode_message3 msg3_bytes bob vk_a n_b with
    | Some msg3 -> (
      (is_corrupt tr (long_term_key_label alice) \/ (event_triggered tr alice (Initiate2 alice bob n_b)))
    )
    | None -> True
  ))
let decode_message3_proof tr msg3_bytes bob alice vk_a n_b =
  reveal_opaque (`%decode_message3) (decode_message3 msg3_bytes bob vk_a n_b);
  match decode_message3 msg3_bytes bob vk_a n_b with
  | None -> ()
  | Some msg3 ->
    parse_wf_lemma message (is_publishable tr) msg3_bytes;
    let signed_part : sig_message3 = { sm3_bob = msg3.m3_bob; sm3_n_b = msg3.m3_n_b } in
    let sig_payload : sig_message = SigMsg3 signed_part in
    serialize_wf_lemma sig_message (is_publishable tr) sig_payload;
    parse_serialize_inv_lemma #bytes sig_message sig_payload
#pop-options

#push-options "--ifuel 2 --fuel 1 --z3rlimit 100"
val decode_y_proof:
  tr:trace -> y_enc:bytes -> sk:bytes -> prin:principal ->
  Lemma
  (requires
    is_private_key_for tr sk (LongTermPkeKey "BAN_CCITT.PkeKey") prin /\
    bytes_invariant tr y_enc
  )
  (ensures (
    match decode_y y_enc sk with
    | Some y -> (
      is_publishable tr y \/
      (exists p_other n_a x_a. event_triggered tr p_other (Initiate1 p_other prin n_a x_a y)) \/
      (exists p_other n_b x_b n_a. event_triggered tr p_other (Respond1 p_other prin n_b x_b y n_a))
    )
    | None -> True
  ))
let decode_y_proof tr y_enc sk prin =
  reveal_opaque (`%decode_y) (decode_y y_enc sk);
  match decode_y y_enc sk with
  | None -> ()
  | Some y -> (
    let Some y_plain = pke_dec sk y_enc in
    let Some y_struct = parse userdata y_plain in
    assert(y_struct.data == y);
    // From bytes_invariant_pke_dec: pke_pred holds OR get_label y_plain can_flow public.
    // In the publishable case, derive is_publishable tr y from parse_wf_lemma.
    FStar.Classical.move_requires (parse_wf_lemma userdata (is_publishable tr)) y_plain
  )
#pop-options
