module DY.Lib.Communication.API.Lemmas

open Comparse
open DY.Core
open DY.Lib.Communication.Core.Extension
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed

open DY.Lib.Communication.API.Invariants
open DY.Lib.Communication.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Layer Setup ***)

class local_extension = {
  local_extension_preds: comm_higher_layer_event_preds
}

(**** Confidential Send and Receive Lemmas ****)

val encrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> 
  pk_receiver:bytes -> nonce:bytes -> payload:bytes ->
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_secret (long_term_key_label sender) tr nonce /\
    nonce `has_usage tr` PkNonce /\
    is_public_key_for tr pk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
    event_triggered tr sender (CommConfSendMsg sender receiver payload)
  )
  (ensures
    is_publishable tr (encrypt_message pk_receiver nonce payload)
  )
let encrypt_message_proof #cinvs tr sender receiver pk_receiver nonce payload = ()

val send_confidential_proof:
  {|invs:protocol_invariants|} ->
  {|lep:local_extension|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  keys_sess_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds /\
    higher_layer_preds.send_conf tr sender receiver payload /\
    lep.local_extension_preds.send_conf tr sender receiver payload /\
    // We only require the payload to flow to the sender and receiver to allow
    // the sender to send a payload readable by other principals. If you want
    // the payload to be only readable by the sender and receiver, you can use
    // the `comm_higher_layer_event_preds` on the protocol level to enforce
    // this. Look into the usage examples of this layer to see how it works.
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
  )
  (ensures (
    let (_, tr_out) = send_confidential keys_sess_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
let send_confidential_proof #invs #lep tr higher_layer_preds keys_sess_ids sender receiver payload =
  match send_confidential keys_sess_ids sender receiver payload tr with
  | (None, tr_out) -> ()
  | (Some _, tr_out) -> (
    let (Some pk_receiver, tr') = get_public_key sender keys_sess_ids.pki (LongTermPkEncKey comm_layer_pkenc_tag) receiver tr in
    let (nonce, tr') = mk_rand PkNonce (long_term_key_label sender) 32 tr' in
    higher_layer_preds.send_conf_later tr tr' sender receiver payload;
    lep.local_extension_preds.send_conf_later tr tr' sender receiver payload;
    let ((), tr') = trigger_event sender (CommConfSendMsg sender receiver payload) tr' in
    assert(event_triggered tr' sender (CommConfSendMsg sender receiver payload));
    encrypt_message_proof tr' sender receiver pk_receiver nonce payload;
    let msg_encrypted = encrypt_message pk_receiver nonce payload in
    let (msg_id, tr') = send_msg msg_encrypted tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


val decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  receiver:principal -> sk_receiver:bytes -> msg_encrypted:bytes ->  
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_private_key_for tr sk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    bytes_invariant tr msg_encrypted
  )
  (ensures (
    match decrypt_message sk_receiver msg_encrypted with
    | Some payload -> (
      exists sender. (
        is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
        (
          event_triggered tr sender (CommConfSendMsg sender receiver payload) \/
          is_publishable tr payload
        )
      )
    )
    | _ -> True
  ))
let decrypt_message_proof #cinvs tr receiver sk_receiver msg_encrypted =
  match decrypt_message sk_receiver msg_encrypted with
  | Some payload -> ()
  | _ -> ()

val receive_confidential_proof:
  {|invs:protocol_invariants|} ->
  {|lep:local_extension|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\ 
    has_private_keys_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds
  )
  (ensures (
    match receive_confidential comm_keys_ids receiver msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some payload, tr_out) -> ( 
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommConfReceiveMsg receiver payload)
    )
  ))
let receive_confidential_proof #invs #lep tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_confidential comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some payload, tr_out) -> (
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (LongTermPkEncKey comm_layer_pkenc_tag) tr in
    let (Some msg_encrypted, tr) = recv_msg msg_id tr in
    decrypt_message_proof tr receiver sk_receiver msg_encrypted;
    let Some msg_plain = decrypt_message sk_receiver msg_encrypted in
    let ((), tr) = trigger_event receiver (CommConfReceiveMsg receiver payload) tr in
    assert(tr_out == tr);
    ()
  )


(**** Authenticated Send and Receive Lemmas ****)

val sign_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> payload:bytes -> is_encrypted:bool ->
  sk_sender:bytes -> nonce:bytes -> 
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_publishable tr payload /\
    is_secret (long_term_key_label sender) tr nonce /\
    nonce `has_usage tr` SigNonce /\
    is_private_key_for tr sk_sender (LongTermSigKey comm_layer_sign_tag) sender /\
    (
      if is_encrypted then (
        match pk_enc_extract_msg payload with
        | None -> False
        | Some plain_payload -> (     
          event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
        )
      ) else (
        event_triggered tr sender (CommAuthSendMsg sender payload)
      )
    )
  )
  (ensures
    is_publishable tr (sign_message sender receiver payload is_encrypted sk_sender nonce)
  )
let sign_message_proof #cinvs tr sender receiver payload is_encrypted sk_sender nonce =
  if is_encrypted then (
    let sig_input = Encrypted {sender; receiver; payload} in
    let sig_input_bytes = serialize signature_input sig_input in
    serialize_wf_lemma signature_input (is_publishable tr) sig_input;
    let signature = sign sk_sender nonce sig_input_bytes in
    let msg_signed = {sender; receiver; payload; signature} in
    assert(bytes_invariant tr signature);
    serialize_wf_lemma communication_message_sign (is_publishable tr) msg_signed;
    ()
  ) else (
    let sig_input = Plain {sender; receiver; payload} in
    let sig_input_bytes = serialize signature_input sig_input in
    serialize_wf_lemma signature_input (is_publishable tr) sig_input;
    let signature = sign sk_sender nonce sig_input_bytes in
    let msg_signed = {sender; receiver; payload; signature} in
    assert(bytes_invariant tr signature);
    serialize_wf_lemma communication_message_sign (is_publishable tr) msg_signed;
    ()
  )

val send_authenticated_proof:
  {|invs:protocol_invariants|} ->
  {|lep:local_extension|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\ 
    has_private_keys_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds /\
    higher_layer_preds.send_auth tr sender payload /\
    is_publishable tr payload
  )
  (ensures (
    let (_, tr_out) = send_authenticated comm_keys_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
let send_authenticated_proof #invs #lep tr higher_layer_preds comm_keys_ids sender receiver payload =
    match send_authenticated comm_keys_ids sender receiver payload tr with
    | (None, tr_out) -> ()
    | (Some _, tr_out) -> (      
      let (Some sk_sender, tr') = get_private_key sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) tr in
      let (nonce,  tr') = mk_rand SigNonce (long_term_key_label sender) 32 tr' in      
      higher_layer_preds.send_auth_later tr tr' sender payload;
      let ((), tr') = trigger_event sender (CommAuthSendMsg sender payload) tr' in
      assert(event_triggered tr' sender (CommAuthSendMsg sender payload));
      sign_message_proof tr' sender receiver payload false sk_sender nonce;
      let msg_signed = sign_message sender receiver payload false sk_sender nonce in
      let (msg_id, tr') = send_msg msg_signed tr' in
      assert(tr_out == tr');
      assert(trace_invariant tr_out);
      ()
    )


val verify_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal ->
  msg_bytes:bytes -> is_encrypted:bool ->
  vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_publishable tr msg_bytes /\
    is_public_key_for tr vk_sender (LongTermSigKey comm_layer_sign_tag) sender    
  )
  (ensures (
    match verify_message receiver msg_bytes is_encrypted vk_sender with
    | Some {sender=sender'; receiver=receiver'; payload} -> (
      is_publishable tr payload /\
      (
        (
          sender' == sender /\
          (
            if is_encrypted then (
              match pk_enc_extract_msg payload with
              | None -> False
              | Some plain_payload -> (
                event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
              )
            ) else (
              event_triggered tr sender (CommAuthSendMsg sender payload)
            )
          )
        ) \/ (
          is_corrupt tr (long_term_key_label sender)
        )
      )
    )
    | _ -> True
  ))
let verify_message_proof #cinvs tr sender receiver msg_bytes is_encrypted vk_sender =
  assert(get_signkey_label tr vk_sender == long_term_key_label sender);
  match verify_message receiver msg_bytes is_encrypted vk_sender with
  | Some {sender=sender'; receiver=receiver'; payload} -> (
    parse_wf_lemma communication_message_sign (is_publishable tr) msg_bytes;
    let Some msg_signed = parse communication_message_sign msg_bytes in
    
    if is_encrypted then (
      let sig_input_e = Encrypted {sender=sender'; receiver=msg_signed.receiver; payload=msg_signed.payload} in
      serialize_wf_lemma signature_input (is_publishable tr) sig_input_e;
      ()
    ) else (
      let sig_input_p = Plain {sender=sender'; receiver=msg_signed.receiver; payload=msg_signed.payload} in
      serialize_wf_lemma signature_input (is_publishable tr) sig_input_p;
      ()
    )
  )
  | _ -> ()

val receive_authenticated_proof:
  {|invs:protocol_invariants|} ->
  {|lep:local_extension|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\ 
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds
  )
  (ensures (
    match receive_authenticated comm_keys_ids receiver msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some {sender; receiver; payload}, tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommAuthReceiveMsg sender receiver payload)
    )
  ))
let receive_authenticated_proof #invs #lep tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_authenticated comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some {sender=sender'; receiver=receiver'; payload}, tr_out) -> (
    let (Some msg_signed, tr) = recv_msg msg_id tr in
    let Some sender = get_sender msg_signed in
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) sender tr in
    verify_message_proof tr sender receiver msg_signed false vk_sender;
    let (Some cm) = verify_message receiver msg_signed false vk_sender in
    let ((), tr) = trigger_event receiver (CommAuthReceiveMsg sender receiver cm.payload) tr in
    assert(tr_out == tr);
    ()
  )


(**** Confidential and Authenticates Send and Receive Lemmas ****)

val encrypt_and_sign_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> payload:bytes ->
  pk_receiver:bytes -> sk_sender:bytes -> enc_nonce:bytes -> sign_nonce:bytes ->
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_secret (long_term_key_label sender) tr enc_nonce /\
    is_secret (long_term_key_label sender) tr sign_nonce /\
    enc_nonce `has_usage tr` PkNonce /\
    sign_nonce `has_usage tr` SigNonce /\
    is_public_key_for tr pk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    is_private_key_for tr sk_sender (LongTermSigKey comm_layer_sign_tag) sender /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
    event_triggered tr sender (CommConfSendMsg sender receiver payload) /\
    event_triggered tr sender (CommConfAuthSendMsg sender receiver payload)
  )
  (ensures
    is_publishable tr (encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce)
  )
let encrypt_and_sign_message_proof #cinvs tr sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce =
  encrypt_message_proof #cinvs tr sender receiver pk_receiver enc_nonce payload;
  let enc_payload = encrypt_message pk_receiver enc_nonce payload in
  pk_enc_extract_msg_enc_lemma pk_receiver enc_nonce payload enc_payload;
  sign_message_proof tr sender receiver enc_payload true sk_sender sign_nonce;
  ()

#push-options "--z3rlimit 10"
val send_confidential_authenticated_proof:
  {|invs:protocol_invariants|} ->
  {|lep:local_extension|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds /\
    higher_layer_preds.send_conf tr sender receiver payload /\
    lep.local_extension_preds.send_conf tr sender receiver payload /\
    higher_layer_preds.send_conf_auth tr sender receiver payload /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
  )
  (ensures (
    let (_, tr_out) = send_confidential_authenticated comm_keys_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
let send_confidential_authenticated_proof #invs #lep tr higher_layer_preds comm_keys_ids sender receiver payload =
  match send_confidential_authenticated comm_keys_ids sender receiver payload tr with
  | (None, tr_out) -> ()
  | (Some _, tr_out) -> (
    let (Some pk_receiver, tr') = get_public_key sender comm_keys_ids.pki (LongTermPkEncKey comm_layer_pkenc_tag) receiver tr in
    let (Some sk_sender, tr') = get_private_key  sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) tr' in
    let (enc_nonce, tr') = mk_rand PkNonce (long_term_key_label sender) 32 tr' in
    let (sign_nonce, tr') = mk_rand SigNonce (long_term_key_label sender) 32 tr' in
    
    higher_layer_preds.send_conf_later tr tr' sender receiver payload;
    lep.local_extension_preds.send_conf_later tr tr' sender receiver payload;
    let ((), tr') = trigger_event sender (CommConfSendMsg sender receiver payload) tr' in
    assert(event_triggered tr' sender (CommConfSendMsg sender receiver payload));    

    higher_layer_preds.send_conf_auth_later tr tr' sender receiver payload;
    let ((), tr') = trigger_event sender (CommConfAuthSendMsg sender receiver payload) tr' in
    assert(event_triggered tr' sender (CommConfAuthSendMsg sender receiver payload));
    
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
  tr:trace ->
  sender:principal -> receiver:principal -> msg_encrypted_signed:bytes ->
  sk_receiver:bytes -> vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_publishable tr msg_encrypted_signed /\
    is_public_key_for tr vk_sender (LongTermSigKey comm_layer_sign_tag) sender /\
    is_private_key_for tr sk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver
  )
  (ensures (
    match verify_and_decrypt_message receiver msg_encrypted_signed sk_receiver vk_sender with
    | None -> True
    | Some {sender=sender'; receiver=receiver'; payload} -> (
      is_knowable_by (principal_label receiver) tr payload /\
      (
        (
          sender' == sender /\
          event_triggered tr sender (CommConfAuthSendMsg sender receiver payload)
        ) \/ (
          is_corrupt tr (long_term_key_label sender)
        )
      )
    )
  ))
let verify_and_decrypt_message_proof #cinvs tr sender receiver msg_encrypted_signed sk_receiver vk_sender =
  match verify_and_decrypt_message receiver msg_encrypted_signed sk_receiver vk_sender with
  | None -> ()
  | Some {sender=sender'; receiver=receiver'; payload} -> (
    verify_message_proof tr sender receiver msg_encrypted_signed true vk_sender;
    let Some {sender=sender''; receiver=receiver''; payload=enc_payload} = verify_message receiver msg_encrypted_signed true vk_sender in    
    decrypt_message_proof tr receiver sk_receiver enc_payload;
    let Some payload' = decrypt_message sk_receiver enc_payload in
    pk_enc_extract_msg_dec_lemma sk_receiver enc_payload payload;
    ()
  )

#push-options "--z3rlimit 10"
val receive_confidential_authenticated_proof:
  {|invs:protocol_invariants|} ->
  {|lep:local_extension|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds
  )
  (ensures
    (
      match receive_confidential_authenticated comm_keys_ids receiver msg_id tr with
      | (None, tr_out) -> trace_invariant tr_out
      | (Some {sender; receiver=receiver'; payload}, tr_out) -> (
        trace_invariant tr_out /\
        event_triggered tr_out receiver (CommConfAuthReceiveMsg sender receiver payload) /\
        is_knowable_by (principal_label receiver) tr payload
      )
    )
  )
let receive_confidential_authenticated_proof #invs #lep tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_confidential_authenticated comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some {sender; receiver=receiver'; payload}, tr_out) -> (
    let (Some msg_encrypted_signed, tr) = recv_msg msg_id tr in
    let Some sender = get_sender msg_encrypted_signed in
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (LongTermPkEncKey comm_layer_pkenc_tag) tr in
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) sender tr in
    verify_and_decrypt_message_proof tr sender receiver msg_encrypted_signed sk_receiver vk_sender;
    let Some msg = verify_and_decrypt_message receiver msg_encrypted_signed sk_receiver vk_sender in
    let ((), tr) = trigger_event receiver (CommConfAuthReceiveMsg msg.sender receiver msg.payload) tr in
    assert(event_triggered tr receiver (CommConfAuthReceiveMsg msg.sender receiver msg.payload));
    assert(trace_invariant tr);
    assert(tr == tr_out);
    ()
  )
#pop-options


(**** Request-Response Pair Lemmas ****)

val compute_request_message_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  id:bytes -> payload:bytes -> key:bytes ->
  Lemma
  (requires
    is_secret (comm_label client server) tr id /\
    is_secret (comm_label client server) tr key /\
    is_knowable_by (comm_label client server) tr payload
  )
  (ensures
    is_knowable_by (comm_label client server) tr (compute_request_message client id payload key)
  )
let compute_request_message_proof #invs tr client server id payload key =
  serialize_wf_lemma request_message (is_knowable_by (comm_label client server) tr) {client; id; payload; key};
  ()

val request_response_event_preconditions: bytes -> bytes -> comm_higher_layer_event_preds
let request_response_event_preconditions id payload = {
  default_comm_higher_layer_event_preds with
  send_conf = (fun tr client server req_payload ->
    event_triggered tr client (CommClientSendRequest client server id payload)
  );
}

#push-options "--fuel 0 --ifuel 2"
instance lep:local_extension = {
  local_extension_preds = {
    default_comm_higher_layer_event_preds with
    send_conf = (fun tr client server req_payload ->
      match decode_request_message req_payload with
      | None -> False
      | Some {id; client=client'; payload; key} -> (
        client == client' /\
        event_triggered tr client (CommClientSendRequest client server id payload)
      )
    )
  }
}
#pop-options


val send_request_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  client:principal -> server:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds /\
    has_communication_layer_state_predicates /\
    higher_layer_preds.send_request tr client server payload /\
    (forall p. higher_layer_preds.send_conf tr client server p) /\
    is_knowable_by (comm_label client server) tr payload
  )
  (ensures (
    let (_, tr_out) = send_request comm_keys_ids client server payload tr in
    trace_invariant tr_out
  ))
let send_request_proof #invs tr comm_keys_ids higher_layer_preds client server payload =
  match send_request comm_keys_ids client server payload tr with
  | (None, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 tr in
    let (id, tr') = mk_rand NoUsage (comm_label client server) 32 tr' in
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {id; server; payload; key} <: communication_states) tr' in
    higher_layer_preds.send_request_later tr tr' client server payload;
    let ((), tr') = trigger_event client (CommClientSendRequest client server id payload) tr' in
    ()
  )
  | (Some _, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 tr in
    let (id, tr') = mk_rand NoUsage (comm_label client server) 32 tr' in
    
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {id; server; payload; key} <: communication_states) tr' in
    
    higher_layer_preds.send_request_later tr tr' client server payload;
    assert(trace_invariant tr');
    assert(is_knowable_by (comm_label client server) tr' payload);
    assert(higher_layer_preds.send_request tr' client server payload);
    let ((), tr') = trigger_event client (CommClientSendRequest client server id payload) tr' in
    assert(trace_invariant tr');
    assert(event_triggered tr' client (CommClientSendRequest client server id payload));
    assert(trace_invariant tr');
        
    compute_request_message_proof tr' client server id payload key;
    let req_payload = compute_request_message client id payload key in

    higher_layer_preds.send_conf_later tr tr' client server req_payload;
    assert(lep.local_extension_preds.send_conf tr' client server req_payload);
    //lep.local_extension_preds.send_conf_later tr tr' client server req_payload;
    assert(higher_layer_preds.send_conf tr' client server req_payload);
    assert(lep.local_extension_preds.send_conf tr' client server req_payload);
    send_confidential_proof #invs #lep tr' higher_layer_preds comm_keys_ids client server req_payload;
    
    let (Some msg_id, tr') = send_confidential comm_keys_ids client server req_payload tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


val decode_request_message_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  server:principal -> msg_bytes:bytes ->
  Lemma
  (requires
    exists client. is_knowable_by (comm_label client server) tr msg_bytes
  )
  (ensures (
    match decode_request_message msg_bytes with
    | None -> True
    | Some {id; client=client'; payload; key} -> (
      exists client.
        is_knowable_by (comm_label client server) tr id /\
        is_knowable_by (comm_label client server) tr payload /\
        is_knowable_by (comm_label client server) tr key
    )
  ))
let decode_request_message_proof #cinvs tr server msg_bytes =
  match decode_request_message msg_bytes with
  | None -> ()
  | Some {id; client=client'; payload; key} -> (
    eliminate exists client. is_knowable_by (comm_label client server) tr msg_bytes
    returns (exists client.
        is_knowable_by (comm_label client server) tr id /\
        is_knowable_by (comm_label client server) tr payload /\
        is_knowable_by (comm_label client server) tr key)
    with _. (
      parse_wf_lemma request_message (is_knowable_by (comm_label client server) tr) msg_bytes;
     ()
    )
  )

#push-options "--z3rlimit 10"
val receive_request_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  server:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates lep.local_extension_preds higher_layer_preds /\
    has_communication_layer_state_predicates
  )
  (ensures (
    match receive_request comm_keys_ids server msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (sid, payload), tr_out) -> (
      trace_invariant tr_out /\
      (exists client. is_knowable_by (comm_label client server) tr_out payload)
    )
  ))
let receive_request_proof #invs tr comm_keys_ids higher_layer_preds server msg_id =
  match receive_request comm_keys_ids server msg_id tr with
  | (None, tr_out) -> ()
  | (Some (sid, payload), tr_out) -> (
    receive_confidential_proof #invs #lep tr higher_layer_preds comm_keys_ids server msg_id;
    let (Some req_msg_bytes, tr) = receive_confidential comm_keys_ids server msg_id tr in
    
    assert(exists client.
      event_triggered tr client (CommConfSendMsg client server req_msg_bytes) \/
          is_publishable tr req_msg_bytes
    );
    assert(exists client.
      lep.local_extension_preds.send_conf tr client server req_msg_bytes \/
          is_publishable tr req_msg_bytes
    );

    decode_request_message_proof tr server req_msg_bytes;
    let Some req_msg = decode_request_message req_msg_bytes in

    FStar.Classical.move_requires (parse_wf_lemma request_message (is_publishable tr)) req_msg_bytes;
    assert(exists client.
      event_triggered tr client (CommClientSendRequest client server req_msg.id req_msg.payload) \/
        is_publishable tr req_msg.payload
    );

    assert(exists client.
      is_knowable_by (comm_label client server) tr req_msg.id /\
      is_knowable_by (comm_label client server) tr req_msg.payload /\
      is_knowable_by (comm_label client server) tr req_msg.key
    );
    
   
    let (sid, tr) = new_session_id server tr in
    assert(trace_invariant tr);
    let ((), tr) = set_state server sid (ServerReceiveRequest {id=req_msg.id; client=req_msg.client; payload=req_msg.payload; key=req_msg.key} <: communication_states) tr in
    assert(trace_invariant tr);

    let ((), tr) = trigger_event server (CommServerReceiveRequest server req_msg.id req_msg.payload) tr in
    assert(trace_invariant tr);
    assert(event_triggered tr server (CommServerReceiveRequest server req_msg.id req_msg.payload));
    
    assert(tr == tr_out);
    assert(trace_invariant tr_out);
    ()
  )
#pop-options
