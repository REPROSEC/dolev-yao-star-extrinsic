module DY.Lib.Communication.Core.Lemmas

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"


/// The communication layer makes use of many lemmas with SMT patterns.
/// These lemmas depend, however, on the communication layer predicates
/// in use for the current analysis.
/// To enable these core lemmas for an analysis, which requires specifying which
/// predicates they shouild be used for, one can use the line
/// `enable_core_comm_layer_lemmas preds`, where `preds` is the relevant
/// `comm_core_higher_layer_event_preds` for the protocol.
/// See https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns
/// for more information on this technique.

[@@"opaque_to_smt"]
val core_comm_layer_lemmas_enabled:
  #a:Type -> {|comm_layer_core_config a|} ->
  comm_core_higher_layer_event_preds a -> prop
let core_comm_layer_lemmas_enabled _ = True

val enable_core_comm_layer_lemmas:
  #a:Type -> {|comm_layer_core_config a|} ->
  preds:comm_core_higher_layer_event_preds a ->
  Lemma (core_comm_layer_lemmas_enabled preds)
let enable_core_comm_layer_lemmas preds =
  normalize_term_spec (core_comm_layer_lemmas_enabled preds)

(**** Initialization Satisfies the Trace Invariants ****)

#push-options "--ifuel 2 --z3rlimit 25"
val initialize_communication_core_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  a:Type -> {|comm_layer_core_config a|} ->
  sender:principal -> receiver:principal ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_private_keys_state_update_invariant /\
    has_pki_invariant /\
    has_pki_state_update_invariant
  )
  (ensures (
    let (_, tr_out) = initialize_communication_core a sender receiver tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant #invs tr);
   SMTPat (initialize_communication_core a sender receiver tr);
  ]
let initialize_communication_core_proof tr a sender receiver =
  reveal_opaque (`%initialize_communication_core) (initialize_communication_core a sender receiver)
#pop-options

(**** Confidential Send and Receive Lemmas ****)

val comm_conf_send_event_triggered:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  trace -> principal -> principal -> a ->
  prop
let comm_conf_send_event_triggered #a tr sender receiver payload =
  event_triggered tr sender (CommConfSendMsg sender receiver payload <: communication_core_event a)

val encrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  sender:principal -> receiver:principal ->
  pk_receiver:bytes -> nonce:bytes -> payload:a ->
  Lemma
  (requires (
    has_communication_layer_core_crypto_predicates a /\
    is_secret (long_term_key_label sender) tr nonce /\
    nonce `has_usage tr` PkeNonce /\
    is_public_key_for tr pk_receiver (LongTermPkeKey (comm_layer_pkenc_tag a)) receiver /\
    is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
    comm_conf_send_event_triggered tr sender receiver payload
  ))
  (ensures
    is_publishable tr (encrypt_message pk_receiver nonce payload) 
  )
let encrypt_message_proof #cinvs #a #config tr sender receiver pk_receiver nonce pkenc_in =
  reveal_opaque (`%encrypt_message) (encrypt_message #a);
  assert(is_well_formed (encryption_input a) #(parseable_serializeable_bytes_encryption_input #a) (is_knowable_by (comm_label sender receiver) tr) (Unsigned pkenc_in));
  ()

val send_confidential_proof:
  {|invs:protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  keys_sess_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:a ->
  Lemma
  (requires (
    trace_invariant tr /\
    has_pki_invariant /\
    has_communication_layer_core_predicates higher_layer_preds /\
    higher_layer_preds.send_conf tr sender receiver payload /\
    // We only require the payload to flow to the sender and receiver to allow
    // the sender to send a payload readable by other principals. If you want
    // the payload to be only readable by the sender and receiver, you can use
    // the `comm_core_higher_layer_event_preds` on the protocol level to enforce
    // this. Look into the usage examples of this layer to see how it works.
    is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload
  ))
  (ensures (
    let (_, tr_out) = send_confidential keys_sess_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant #invs tr);
   SMTPat (send_confidential keys_sess_ids sender receiver payload tr);
   SMTPat (core_comm_layer_lemmas_enabled higher_layer_preds)]
let send_confidential_proof #invs #a tr higher_layer_preds keys_sess_ids sender receiver payload =
  reveal_opaque (`%send_confidential) (send_confidential #a);
  match send_confidential keys_sess_ids sender receiver payload tr with
  | (None, tr_out) -> ()
  | (Some _, tr_out) -> (
    let (Some pk_receiver, tr') = get_public_key sender keys_sess_ids.pki (LongTermPkeKey (comm_layer_pkenc_tag a)) receiver tr in
    let (nonce, tr') = mk_rand PkeNonce (long_term_key_label sender) 32 tr' in
    higher_layer_preds.send_conf_later tr tr' sender receiver payload;
    let ((), tr') = trigger_event sender (CommConfSendMsg sender receiver payload <: communication_core_event a) tr' in
    encrypt_message_proof tr' sender receiver pk_receiver nonce payload;
    let msg_encrypted = encrypt_message pk_receiver nonce payload in
    let (msg_id, tr') = send_msg msg_encrypted tr' in
    assert(tr_out == tr');
    ()
  )

val decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  tr:trace ->
  receiver:principal -> sk_receiver:bytes -> msg_encrypted:bytes ->
  Lemma
  (requires
    has_communication_layer_core_crypto_predicates a /\
    is_private_key_for tr sk_receiver (LongTermPkeKey (comm_layer_pkenc_tag a)) receiver /\
    bytes_invariant tr msg_encrypted
  )
  (ensures
    (
      match decrypt_message #a sk_receiver msg_encrypted with
      | None -> True
      | Some payload -> (exists sender.
        is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
        (
          comm_conf_send_event_triggered tr sender receiver payload \/
          is_well_formed a (is_publishable tr) payload
        )
      )
    )
  )
let decrypt_message_proof #cinvs #a tr receiver sk_receiver msg_encrypted =
  reveal_opaque (`%decrypt_message) (decrypt_message #a);
  match decrypt_message #a sk_receiver msg_encrypted with
  | None -> ()
  | Some payload -> (
    let Some plaintext = pke_dec sk_receiver msg_encrypted in
    let Some payload = parse (encryption_input a) plaintext in
    let Unsigned payload = payload in
    assert(exists sender. is_knowable_by (comm_label sender receiver) tr plaintext);
    eliminate exists sender. is_knowable_by (comm_label sender receiver) tr plaintext /\ 
      (event_triggered tr sender (CommConfSendMsg sender receiver payload <: communication_core_event a) \/
          is_publishable tr plaintext)
    returns exists sender. is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
            (
              comm_conf_send_event_triggered tr sender receiver payload \/
              is_well_formed a (is_publishable tr) payload
            )
    with _. (
      parse_wf_lemma (encryption_input a) (is_knowable_by (comm_label sender receiver) tr) plaintext;
      FStar.Classical.move_requires (parse_wf_lemma (encryption_input a) (is_publishable tr)) plaintext;
      ()
    )
  )

val receive_confidential_proof:
  {|invs:protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_communication_layer_core_predicates higher_layer_preds
  )
  (ensures (
    match receive_confidential comm_keys_ids receiver msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some payload, tr_out) ->
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommConfReceiveMsg receiver payload <: communication_core_event a) /\
      is_well_formed a (is_knowable_by (principal_label receiver) tr_out) payload
  ))
  [SMTPat (trace_invariant tr);
   SMTPat (receive_confidential #a comm_keys_ids receiver msg_id tr);
   SMTPat (core_comm_layer_lemmas_enabled higher_layer_preds)]
let receive_confidential_proof #invs #a tr higher_layer_preds comm_keys_ids receiver msg_id =
  reveal_opaque (`%receive_confidential) (receive_confidential #a);
  match receive_confidential comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some payload, tr_out) -> (
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (LongTermPkeKey (comm_layer_pkenc_tag a)) tr in
    let (Some msg_encrypted, tr) = recv_msg msg_id tr in
    decrypt_message_proof #invs.crypto_invs #a tr receiver sk_receiver msg_encrypted;
    let Some msg_plain = decrypt_message #a sk_receiver msg_encrypted in
    let ((), tr) = trigger_event receiver (CommConfReceiveMsg receiver payload <: communication_core_event a) tr in
    assert(tr_out == tr);
    assert(trace_invariant tr_out);
    ()
  )


(**** Authenticated Send and Receive Lemmas ****)

val comm_auth_send_event_triggered:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  trace -> principal -> principal -> a ->
  prop
let comm_auth_send_event_triggered #a tr sender receiver payload =
  event_triggered tr sender (CommAuthSendMsg sender receiver payload <: communication_core_event a)

val comm_conf_auth_send_event_triggered:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  trace -> principal -> principal -> a ->
  prop
let comm_conf_auth_send_event_triggered #a tr sender receiver payload =
  event_triggered tr sender (CommConfAuthSendMsg sender receiver payload <: communication_core_event a)

#push-options "--ifuel 1 --fuel 0 --z3rlimit 50"
val sign_message_proof:
  {|cinvs:crypto_invariants|} ->
  #a:Type0 -> {|config:comm_layer_core_config a|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> input:either a (bytes & bytes) ->
  sk_sender:bytes -> nonce:bytes ->
  Lemma
  (requires (
    has_communication_layer_core_crypto_predicates a /\
    is_secret (long_term_key_label sender) tr nonce /\
    nonce `has_usage tr` SigNonce /\
    is_private_key_for tr sk_sender (LongTermSigKey (comm_layer_sign_tag a)) sender /\
    (
      match input with
      | Inl payload -> (
        is_well_formed a (is_publishable tr) payload /\
        comm_auth_send_event_triggered #a tr sender receiver payload
      )
      | Inr (payload, pk) -> (
        is_publishable tr payload /\
        is_publishable tr pk /\
        (exists plain_payload nonce.
          payload == pke_enc pk nonce plain_payload /\
          (match parse (encryption_input a) plain_payload with
          | Some (Signed sender' receiver' plain_payload_parsed) -> (
            sender == sender' /\ receiver == receiver' /\
            comm_conf_auth_send_event_triggered tr sender receiver plain_payload_parsed
          )
          | _ -> False)
        )
      )
    )
  ))
  (ensures
    is_publishable tr (sign_message sender receiver input sk_sender nonce)
  )
let sign_message_proof #cinvs #a #config tr sender receiver input sk_sender nonce =
  reveal_opaque (`%sign_message) (sign_message #a);
  // The proof is duplicated here to improve the proof performance
  match input with
    | Inl payload -> (
      let sig_input:signature_input a = Plain sender receiver payload in
      let sig_input_bytes = serialize (signature_input a) sig_input in
      serialize_wf_lemma (signature_input a) (is_publishable tr) sig_input;
      let signature = sign sk_sender nonce sig_input_bytes in
      assert(bytes_invariant tr signature); // Improves proof performance
      let msg_signed = SigMessage {msg=sig_input_bytes; signature} in
      serialize_wf_lemma comm_message_t (is_publishable tr) msg_signed;
      ()
    )
    | Inr (payload, pk) -> (
      let sig_input:signature_input a = Encrypted payload pk in
      let sig_input_bytes = serialize (signature_input a) sig_input in
      serialize_wf_lemma (signature_input a) (is_publishable tr) sig_input;
      let signature = sign sk_sender nonce sig_input_bytes in
      assert(bytes_invariant tr signature); // Improves proof performance
      let msg_signed = SigMessage {msg=sig_input_bytes; signature} in
      serialize_wf_lemma comm_message_t (is_publishable tr) msg_signed;
      ()
    )
#pop-options

val send_authenticated_proof:
  {|invs:protocol_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  comm_keys_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_communication_layer_core_predicates higher_layer_preds /\
    higher_layer_preds.send_auth tr sender receiver payload /\
    is_well_formed a (is_publishable tr) payload
  )
  (ensures (
    let (_, tr_out) = send_authenticated comm_keys_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant #invs tr);
   SMTPat (send_authenticated comm_keys_ids sender receiver payload tr);
   SMTPat (core_comm_layer_lemmas_enabled higher_layer_preds)]
let send_authenticated_proof #invs #a tr higher_layer_preds comm_keys_ids sender receiver payload =
  reveal_opaque (`%send_authenticated) (send_authenticated #a);
  match send_authenticated comm_keys_ids sender receiver payload tr with
  | (None, tr_out) -> ()
  | (Some _, tr_out) -> (
    let (Some sk_sender, tr') = get_private_key sender comm_keys_ids.private_keys (LongTermSigKey (comm_layer_sign_tag a)) tr in
    let (nonce,  tr') = mk_rand SigNonce (long_term_key_label sender) 32 tr' in
    higher_layer_preds.send_auth_later tr tr' sender receiver payload;
    let ((), tr') = trigger_event sender (CommAuthSendMsg sender receiver payload <: communication_core_event a) tr' in
    assert(comm_auth_send_event_triggered tr' sender receiver payload);
    sign_message_proof #invs.crypto_invs #a tr' sender receiver (Inl payload) sk_sender nonce;
    let msg_signed = sign_message #a sender receiver (Inl payload) sk_sender nonce in
    let (msg_id, tr') = send_msg msg_signed tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


#push-options "--z3rlimit 20"
val verify_message_proof:
  {|cinvs:crypto_invariants|} ->
  #a:Type -> {|config:comm_layer_core_config a|} ->
  tr:trace ->
  sender:principal -> receiver:principal ->
  msg_bytes:bytes -> sk_receiver_opt:option bytes ->
  vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_core_crypto_predicates a /\
    is_publishable tr msg_bytes /\
    is_public_key_for tr vk_sender (LongTermSigKey (comm_layer_sign_tag a)) sender /\
    Some sender == get_sender #a msg_bytes sk_receiver_opt
  )
  (ensures (
    match verify_message #a sender receiver msg_bytes sk_receiver_opt vk_sender with
    | Some payload -> (
      let Some (SigMessage msg_signed) = parse comm_message_t msg_bytes in
      let Some sign_input = parse (signature_input a) msg_signed.msg in
      (
        match sign_input, sk_receiver_opt with
        | Plain sender' receiver' payload_bytes', None -> (
          is_well_formed a (is_publishable tr) (Inl?.v payload) /\
          (
            sender == sender' /\
            receiver == receiver' /\
            comm_auth_send_event_triggered tr sender receiver (Inl?.v payload) \/ 
            is_corrupt tr (long_term_key_label sender)
          )
        )
        | Encrypted payload_bytes' pk_receiver, Some sk_receiver -> (
          is_publishable tr (Inr?.v payload) /\
          ( 
            let Some plaintext = pke_dec sk_receiver payload_bytes' in
            let Some enc_input = parse (encryption_input a) plaintext in
            let Signed sender' receiver' plain_payload_parsed = enc_input in
            sender == sender' /\ receiver == receiver' /\
            (comm_conf_auth_send_event_triggered tr sender receiver plain_payload_parsed \/
              is_corrupt tr (long_term_key_label sender))
              
          )
        )
        | _ -> False
      )
    )
    | _ -> True
  ))
let verify_message_proof #cinvs #a #config tr sender receiver msg_bytes sk_receiver_opt vk_sender =
  assert(get_signkey_label tr vk_sender == long_term_key_label sender);
  match verify_message #a sender receiver msg_bytes sk_receiver_opt vk_sender with
  | None -> ()
  | Some payload -> (
    parse_wf_lemma comm_message_t (is_publishable tr) msg_bytes;
    let Some msg_signed_t = parse comm_message_t msg_bytes in
    let SigMessage msg_signed = msg_signed_t in
    parse_wf_lemma (signature_input a) (is_publishable tr) msg_signed.msg;
    let Some sign_input = parse (signature_input a) msg_signed.msg in
    match sign_input, sk_receiver_opt with
    | Plain sender' receiver' payload_bytes', None -> (
      ()
    )
    | Encrypted payload_bytes pk_receiver, Some sk_receiver -> (
      let Some plaintext = pke_dec sk_receiver payload_bytes in
      let Some enc_input = parse (encryption_input a) plaintext in
      let Signed sender' receiver' plain_payload_parsed = enc_input in
      eliminate (
          exists plain_payload nonce.
          payload_bytes == pke_enc pk_receiver nonce plain_payload /\
          (match parse (encryption_input a) plain_payload with
          | Some (Signed sender'' receiver'' plain_payload_parsed) -> (
            event_triggered tr sender'' (CommConfAuthSendMsg sender'' receiver'' plain_payload_parsed <: communication_core_event a)
          ) 
          | _ -> False)
        ) \/ is_corrupt tr (long_term_key_label sender)
      returns (comm_conf_auth_send_event_triggered tr sender receiver plain_payload_parsed \/
                  is_corrupt tr (long_term_key_label sender))
      with _. (
        eliminate exists (plain_payload:bytes). (exists (nonce:bytes).
          payload_bytes == pke_enc pk_receiver nonce plain_payload /\
          (match parse (encryption_input a) plain_payload with
          | Some (Signed sender'' receiver'' plain_payload_parsed) -> (
            event_triggered tr sender'' (CommConfAuthSendMsg sender'' receiver'' plain_payload_parsed <: communication_core_event a)
          ) 
          | _ -> False))
        returns _
        with _. (
          eliminate exists (nonce:bytes).
          payload_bytes == pke_enc pk_receiver nonce plain_payload /\
          (match parse (encryption_input a) plain_payload with
          | Some (Signed sender'' receiver'' plain_payload_parsed) -> (
            event_triggered tr sender'' (CommConfAuthSendMsg sender'' receiver'' plain_payload_parsed <: communication_core_event a)
          ) 
          | _ -> False)
          returns _
          with _. (
            pke_dec_enc sk_receiver nonce plain_payload;
            () 
          )
        )
      )
      and _. ()
    )
    | _ -> ()
  )
#pop-options

#push-options "--z3rlimit 25"
val receive_authenticated_proof:
  {|invs:protocol_invariants|} ->
  #a:Type -> {|config:comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_communication_layer_core_predicates higher_layer_preds
  )
  (ensures (
    match receive_authenticated comm_keys_ids receiver msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some cm, tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommAuthReceiveMsg cm.sender receiver cm.payload <: communication_core_event a)
    )
  ))
  [SMTPat (trace_invariant #invs tr);
   SMTPat (receive_authenticated #a comm_keys_ids receiver msg_id tr);
   SMTPat (core_comm_layer_lemmas_enabled higher_layer_preds)]
let receive_authenticated_proof #invs #a tr higher_layer_preds comm_keys_ids receiver msg_id =
  reveal_opaque (`%receive_authenticated) (receive_authenticated #a);
  match receive_authenticated #a comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some cm', tr_out) -> (
    let (Some msg_signed_bytes, tr) = recv_msg msg_id tr in
    let Some sender = get_sender #a msg_signed_bytes None in
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (LongTermSigKey (comm_layer_sign_tag a)) sender tr in
    verify_message_proof #invs.crypto_invs #a tr sender receiver msg_signed_bytes None vk_sender;
    match verify_message #a sender receiver msg_signed_bytes None vk_sender with
    | None -> ()
    | Some (Inl payload) -> (
      let ((), tr) = trigger_event receiver (CommAuthReceiveMsg sender receiver payload <: communication_core_event a) tr in
      assert(tr_out == tr);
      assert(trace_invariant tr_out);
    ()
    )
  )
#pop-options


(**** Confidential and Authenticates Send and Receive Lemmas ****)

val encrypt_and_sign_message_proof:
  {|cinvs:crypto_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> payload:a ->
  pk_receiver:bytes -> sk_sender:bytes -> enc_nonce:bytes -> sign_nonce:bytes ->
  Lemma
  (requires
    has_communication_layer_core_crypto_predicates a /\
    is_secret (long_term_key_label sender) tr enc_nonce /\
    is_secret (long_term_key_label sender) tr sign_nonce /\
    enc_nonce `has_usage tr` PkeNonce /\
    sign_nonce `has_usage tr` SigNonce /\
    is_public_key_for tr pk_receiver (LongTermPkeKey (comm_layer_pkenc_tag a)) receiver /\
    is_private_key_for tr sk_sender (LongTermSigKey (comm_layer_sign_tag a)) sender /\
    is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
    comm_conf_auth_send_event_triggered tr sender receiver payload
  )
  (ensures
    is_publishable tr (encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce)
  )
let encrypt_and_sign_message_proof #cinvs #a tr sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce =
  reveal_opaque (`%encrypt_and_sign_message) (encrypt_and_sign_message #a);
  assert(is_well_formed (encryption_input a) #(parseable_serializeable_bytes_encryption_input #a) (is_knowable_by (comm_label sender receiver) tr) (Signed sender receiver payload));
  let enc_payload = pke_enc pk_receiver enc_nonce (serialize (encryption_input a) (Signed sender receiver payload)) in
  sign_message_proof #cinvs #a tr sender receiver (Inr (enc_payload, pk_receiver)) sk_sender sign_nonce;
  ()

#push-options "--z3rlimit 50"
val send_confidential_authenticated_proof:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|}  ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  comm_keys_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_core_predicates higher_layer_preds /\
    higher_layer_preds.send_conf_auth tr sender receiver payload /\
    is_well_formed a (is_knowable_by (join (principal_label sender) (principal_label receiver)) tr) payload
  )
  (ensures (
    let (_, tr_out) = send_confidential_authenticated comm_keys_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr);
   SMTPat (send_confidential_authenticated comm_keys_ids sender receiver payload tr);
   SMTPat (core_comm_layer_lemmas_enabled higher_layer_preds)]
let send_confidential_authenticated_proof #invs #a tr higher_layer_preds comm_keys_ids sender receiver payload =
  reveal_opaque (`%send_confidential_authenticated) (send_confidential_authenticated #a);
  match send_confidential_authenticated comm_keys_ids sender receiver payload tr with
  | (None, tr_out) -> ()
  | (Some _, tr_out) -> (
    let (Some pk_receiver, tr') = get_public_key sender comm_keys_ids.pki (LongTermPkeKey (comm_layer_pkenc_tag a)) receiver tr in
    let (Some sk_sender, tr') = get_private_key  sender comm_keys_ids.private_keys (LongTermSigKey (comm_layer_sign_tag a)) tr' in
    let (enc_nonce, tr') = mk_rand PkeNonce (long_term_key_label sender) 32 tr' in
    let (sign_nonce, tr') = mk_rand SigNonce (long_term_key_label sender) 32 tr' in

    higher_layer_preds.send_conf_auth_later tr tr' sender receiver payload;
    let ((), tr') = trigger_event sender (CommConfAuthSendMsg sender receiver payload <: communication_core_event a) tr' in
    assert(comm_conf_auth_send_event_triggered tr' sender receiver payload);

    encrypt_and_sign_message_proof tr' sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce;
    let msg = encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce in
    let (msg_id, tr') = send_msg msg tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )
#pop-options


val verify_and_decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> msg_encrypted_signed:bytes ->
  sk_receiver:bytes -> vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_core_crypto_predicates a /\
    is_publishable tr msg_encrypted_signed /\
    is_private_key_for tr sk_receiver (LongTermPkeKey (comm_layer_pkenc_tag a)) receiver /\
    is_public_key_for tr vk_sender (LongTermSigKey (comm_layer_sign_tag a)) sender /\
    Some sender == get_sender #a msg_encrypted_signed (Some sk_receiver)
  )
  (ensures (
    match verify_and_decrypt_message #a sender receiver sk_receiver vk_sender msg_encrypted_signed with
    | None -> True
    | Some cm -> (
      (
        comm_conf_auth_send_event_triggered tr sender receiver cm.payload \/
        is_well_formed a (is_publishable tr) cm.payload
      ) /\ (
        comm_conf_auth_send_event_triggered tr sender receiver cm.payload \/
        is_corrupt tr (long_term_key_label sender)
      )
    )
  ))
let verify_and_decrypt_message_proof #cinvs #a tr sender receiver msg_encrypted_signed sk_receiver vk_sender =
  reveal_opaque (`%verify_and_decrypt_message) (verify_and_decrypt_message #a);
  reveal_opaque (`%decrypt_message) (decrypt_message #a);
  match verify_and_decrypt_message #a sender receiver sk_receiver vk_sender msg_encrypted_signed with
  | None -> ()
  | Some cm -> (
    verify_message_proof #cinvs #a tr sender receiver msg_encrypted_signed (Some sk_receiver) vk_sender;
    let Some (Inr payload_enc) = verify_message #a sender receiver msg_encrypted_signed (Some sk_receiver) vk_sender in
    let Some msg_signed_t = parse comm_message_t msg_encrypted_signed in
    let SigMessage msg_signed = msg_signed_t in
    let Some sign_input = parse (signature_input a) msg_signed.msg in
    let Encrypted _ pk_receiver = sign_input in
    assert(pk_receiver == pk sk_receiver);

    let Some plaintext = pke_dec sk_receiver payload_enc in
    let Some payload = parse (encryption_input a) plaintext in
    let Signed sender receiver payload = payload in

    FStar.Classical.move_requires (parse_wf_lemma (encryption_input a) (is_publishable tr)) plaintext;
    assert(event_triggered tr sender (CommConfAuthSendMsg sender receiver payload <: communication_core_event a) \/ is_well_formed a (is_publishable tr) payload);
    ()
  )

#push-options "--z3rlimit 50"
val receive_confidential_authenticated_proof:
  {|invs:protocol_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_core_predicates higher_layer_preds
  )
  (ensures(
    match receive_confidential_authenticated #a comm_keys_ids receiver msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some cm, tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommConfAuthReceiveMsg cm.sender receiver cm.payload <: communication_core_event a)
    )
  ))
  [SMTPat (trace_invariant #invs tr);
   SMTPat (receive_confidential_authenticated #a comm_keys_ids receiver msg_id tr);
   SMTPat (core_comm_layer_lemmas_enabled higher_layer_preds)]
let receive_confidential_authenticated_proof #invs #a tr higher_layer_preds comm_keys_ids receiver msg_id =
  reveal_opaque (`%receive_confidential_authenticated) (receive_confidential_authenticated #a);
  reveal_opaque (`%verify_and_decrypt_message) (verify_and_decrypt_message #a); // TODO: These reveals should be removeable.
  match receive_confidential_authenticated #a comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some cm, tr_out) -> (
    let (Some msg_encrypted_signed, tr) = recv_msg msg_id tr in
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (LongTermPkeKey (comm_layer_pkenc_tag a)) tr in
    let Some sender = get_sender #a msg_encrypted_signed (Some sk_receiver) in
    assert(sender == cm.sender);
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (LongTermSigKey (comm_layer_sign_tag a)) sender tr in
    verify_and_decrypt_message_proof #invs.crypto_invs #a tr sender receiver msg_encrypted_signed sk_receiver vk_sender;
    let Some cm = verify_and_decrypt_message #a sender receiver sk_receiver vk_sender msg_encrypted_signed in
    let ((), tr) = trigger_event receiver (CommConfAuthReceiveMsg sender receiver cm.payload <: communication_core_event a) tr in
    assert(trace_invariant tr);
    assert(tr == tr_out);
    ()
  )
#pop-options
