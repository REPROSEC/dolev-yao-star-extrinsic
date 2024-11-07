module DY.Lib.Communication.API.Lemmas

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed

open DY.Lib.Communication.API.Invariants
open DY.Lib.Communication.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(**** Confidential Send and Receive Lemmas ****)

val encrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> 
  pk_receiver:bytes -> nonce:bytes -> payload:bytes ->
  Lemma
  (requires
    has_communication_layer_invariants /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
    is_secret (long_term_key_label sender) tr nonce /\
    nonce `has_usage tr` PkNonce /\
    is_public_key_for tr pk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    event_triggered tr sender (CommConfSendMsg sender receiver payload)
  )
  (ensures
    is_publishable tr (encrypt_message pk_receiver nonce payload)
  )
let encrypt_message_proof #cinvs tr sender receiver pk_receiver nonce payload = ()

val send_confidential_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  keys_sess_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_communication_layer_invariants /\
    comm_layer_preds_later tr (higher_layer_preds.send_conf sender receiver payload) /\
    has_communication_layer_event_predicates higher_layer_preds /\
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
let send_confidential_proof #invs tr higher_layer_preds keys_sess_ids sender receiver payload =
  match send_confidential keys_sess_ids sender receiver payload tr with
  | (None, tr_out) -> ()
  | (Some _, tr_out) -> (
    let (Some pk_receiver, tr) = get_public_key sender keys_sess_ids.pki (LongTermPkEncKey comm_layer_pkenc_tag) receiver tr in
    let (nonce, tr) = mk_rand PkNonce (long_term_key_label sender) 32 tr in
    let ((), tr) = trigger_event sender (CommConfSendMsg sender receiver payload) tr in
    let msg_encrypted = encrypt_message pk_receiver nonce payload in
    assert(higher_layer_preds.send_conf sender receiver payload tr);
    assert(event_triggered tr sender (CommConfSendMsg sender receiver payload));
    encrypt_message_proof tr sender receiver pk_receiver nonce payload;
    let (msg_id, tr) = send_msg msg_encrypted tr in
    assert(tr_out == tr);
    ()
  )

val decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  receiver:principal -> sk_receiver:bytes -> msg_encrypted:bytes ->  
  Lemma
  (requires
    has_communication_layer_invariants /\
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
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\ 
    has_private_keys_invariant /\
    has_communication_layer_invariants /\
    has_communication_layer_event_predicates higher_layer_preds
  )
  (ensures (
    match receive_confidential comm_keys_ids receiver msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some payload, tr_out) -> ( 
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommConfReceiveMsg receiver payload)
    )
  ))
let receive_confidential_proof #invs tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_confidential comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some payload, tr_out) -> (
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (LongTermPkEncKey comm_layer_pkenc_tag) tr in
    let (Some msg_encrypted, tr) = recv_msg msg_id tr in
    let Some msg_plain = decrypt_message sk_receiver msg_encrypted in
    decrypt_message_proof tr receiver sk_receiver msg_encrypted;
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
    has_communication_layer_invariants /\
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
    serialize_wf_lemma communication_message_sign (is_publishable tr) msg_signed;
    ()
  )

val send_authenticated_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\ has_private_keys_invariant /\
    has_communication_layer_invariants /\
    //if_comm_conf_payload sender receiver payload tr /\
    //comm_layer_preds_later tr (if_comm_conf_payload sender receiver payload) /\
    comm_layer_preds_later tr (higher_layer_preds.send_auth sender payload) /\
    has_communication_layer_event_predicates higher_layer_preds /\
    is_publishable tr payload
  )
  (ensures (
    let (_, tr_out) = send_authenticated comm_keys_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
let send_authenticated_proof #invs tr higher_layer_preds comm_keys_ids sender receiver payload =
    match send_authenticated comm_keys_ids sender receiver payload tr with
    | (None, tr_out) -> ()
    | (Some _, tr_out) -> (      
      let (Some sk_sender, tr) = get_private_key sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) tr in
      let (nonce,  tr) = mk_rand SigNonce (long_term_key_label sender) 32 tr in      
      let ((), tr) = trigger_event sender (CommAuthSendMsg sender payload) tr in
      assert(event_triggered tr sender (CommAuthSendMsg sender payload)); 
      let msg_signed = sign_message sender receiver payload false sk_sender nonce in
      sign_message_proof tr sender receiver payload false sk_sender nonce;
      let (msg_id, tr) = send_msg msg_signed tr in
      assert(tr_out == tr);
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
    has_communication_layer_invariants /\
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
    //assert(is_publishable tr payload);
    let Some msg_signed = parse communication_message_sign msg_bytes in
    
    //assert(bytes_invariant tr vk_sender);
    //assert(bytes_invariant tr msg_bytes);
    //assert(bytes_invariant tr msg_signed.signature);
    //normalize_term_spec bytes_invariant;
    //reveal_opaque (`%verify) (verify);
    

    (*assert(event_triggered tr sender (CommAuthSendMsg sender payload) \/
      get_signkey_label vk_sender `can_flow tr` public);
    
    let DY.Core.Bytes.Type.Sign sk nonce sig_input_bytes = msg_signed.signature in
    assert(sign_pred.pred tr (Vk sk) sig_input_bytes \/
      get_signkey_label vk_sender `can_flow tr` public);

    assert(receiver == receiver');
    assert(sender == sender' \/
      get_signkey_label vk_sender `can_flow tr` public);*)
    
    if is_encrypted then (
      let sig_input_e = Encrypted {sender=sender'; receiver=msg_signed.receiver; payload=msg_signed.payload} in
      //let sig_input_bytes_e = serialize signature_input #parseable_serializeable_bytes_signature_input sig_input_e in
      serialize_wf_lemma signature_input (is_publishable tr) sig_input_e;
      //assert(verify vk_sender sig_input_bytes_e msg_signed.signature);      
      //assert(bytes_invariant tr sig_input_bytes_e);      
      //bytes_invariant_verify tr vk_sender sig_input_bytes_e msg_signed.signature;

      (*let Some sig_input = parse signature_input sig_input_bytes in
      assert(Encrypted? sig_input);
      let sig_input_record = Encrypted?.msg sig_input in
      assert(sign_pred.pred tr (Vk sk) sig_input_bytes \/
        get_signkey_label vk_sender `can_flow tr` public);
      assert(msg_signed.receiver == receiver);
      let sig_input' = Encrypted {sender=sender'; receiver=msg_signed.receiver; payload=msg_signed.payload} in
      let sig_input_bytes' = serialize signature_input sig_input' in
      assert(verify vk_sender sig_input_bytes' msg_signed.signature);
      assert(sig_input_record.sender == sender \/
        get_signkey_label vk_sender `can_flow tr` public);
      assert(event_triggered tr sender (CommConfSendMsg sender receiver msg) \/
        get_signkey_label (Vk sk) `can_flow tr` public);*)
      ()
    ) else (
      let sig_input_p = Plain {sender=sender'; receiver=msg_signed.receiver; payload=msg_signed.payload} in
      serialize_wf_lemma signature_input (is_publishable tr) sig_input_p;
      ()
    )
  )
  | _ -> ()

(*val extract_data_from_msg_id:
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  (principal -> principal -> bytes -> prop) ->
  prop
let extract_data_from_msg_id tr comm_keys_ids receiver msg_id fn =
  match recv_msg msg_id tr with
  | (None, tr) -> True
  | (Some msg_signed, tr) -> (
    match get_sender msg_signed with
    | None -> True
    | Some sender -> (
      match get_public_key receiver comm_keys_ids.pki (Verify comm_layer_sign_tag) sender tr with
      | (None, tr) -> True
      | (Some vk_sender, tr) -> (
        match verify_message receiver msg_signed false vk_sender with
        | None -> True
        | Some {sender=sender'; receiver=receiver'; payload} -> (
          fn sender receiver payload
        )
      )
    )
  )*)

val receive_authenticated_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\ has_pki_invariant /\
    has_communication_layer_invariants /\
    has_communication_layer_event_predicates higher_layer_preds
  )
  (ensures (
    match receive_authenticated comm_keys_ids receiver msg_id tr with
    | (Some {sender; receiver; payload}, tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommAuthReceiveMsg sender receiver payload)
    )
    | (None, tr_out) -> trace_invariant tr_out
  ))
let receive_authenticated_proof #invs tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_authenticated comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some {sender=sender'; receiver=receiver'; payload}, tr_out) -> (
    let (Some msg_signed, tr) = recv_msg msg_id tr in
    let Some msg = parse_sig_message msg_signed in
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) msg.sender tr in
    verify_message_proof tr msg.sender receiver msg_signed false vk_sender;
    let ((), tr) = trigger_event receiver (CommAuthReceiveMsg msg.sender receiver payload) tr in
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
    has_communication_layer_invariants /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
    is_secret (long_term_key_label sender) tr enc_nonce /\
    is_secret (long_term_key_label sender) tr sign_nonce /\
    enc_nonce `has_usage tr` PkNonce /\
    sign_nonce `has_usage tr` SigNonce /\
    is_public_key_for tr pk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    is_private_key_for tr sk_sender (LongTermSigKey comm_layer_sign_tag) sender /\
    event_triggered tr sender (CommConfSendMsg sender receiver payload) /\
    event_triggered tr sender (CommAuthSendMsg sender payload) /\
    event_triggered tr sender (CommConfAuthSendMsg sender receiver payload)
  )
  (ensures
    is_publishable tr (encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce)
  )
let encrypt_and_sign_message_proof #cinvs tr sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce =
  encrypt_message_proof #cinvs tr sender receiver pk_receiver enc_nonce payload;
  let enc_payload = encrypt_message pk_receiver enc_nonce payload in
  assert(get_label tr sk_sender == long_term_key_label sender);
  assert(is_publishable tr enc_payload);
  assert(enc_payload == encrypt_message pk_receiver enc_nonce payload);
  assert(event_triggered tr sender (CommConfSendMsg sender receiver payload));
  assert(event_triggered tr sender (CommAuthSendMsg sender payload));
  assert(get_label tr payload `can_flow tr` (join (principal_label sender) (principal_label receiver)));
  //normalize_term_spec pk_dec;
  //normalize_term_spec pk_enc;
  //normalize_term_spec get_sk_label;
  //normalize_term_spec get_sk_usage;
  //normalize_term_spec pk;

  (*assert(match pk_receiver with
  | DY.Core.Bytes.Type.Pk sk -> get_usage sk == PkKey comm_layer_pkenc_tag empty
  | _ -> False);
  assert(match pk_receiver with
  | DY.Core.Bytes.Type.Pk sk -> get_label sk == principal_label receiver
  | _ -> False);

  assert(is_publishable tr enc_payload);

  assert(enc_payload == pk_enc pk_receiver enc_nonce payload);

  
    
  eliminate exists sk_receiver. get_label sk_receiver == principal_label receiver
  returns exists sk_receiver. pk_dec sk_receiver (pk_enc pk_receiver enc_nonce payload) == Some payload
  with _. (
    pk_dec_enc sk_receiver enc_nonce payload;
    assert(
        pk_dec sk_receiver (pk_enc (pk sk_receiver) enc_nonce payload) == Some payload
    );
    assert(Some payload == decrypt_message sk_receiver enc_payload);
    assert(exists plain_msg.
      Some plain_msg == decrypt_message sk_receiver enc_payload
    );
    assert(exists plain_msg.
      get_label plain_msg `can_flow tr` (join (principal_label sender) (principal_label receiver)));

    

    assert(has_communication_layer_invariants cinvs /\
      is_publishable tr enc_payload /\
      is_secret (principal_label sender) tr sign_nonce /\
      SigNonce? (get_usage sign_nonce) /\
      is_signature_key (SigKey comm_layer_sign_tag empty) (principal_label sender) tr sk_sender /\
      (
        if true then (
          (exists sk_receiver plain_msg.
            Some plain_msg == pk_dec sk_receiver enc_payload /\
            get_label sk_receiver == principal_label receiver /\
            event_triggered tr sender (CommConfSendMsg sender receiver plain_msg) /\
            event_triggered tr sender (CommAuthSendMsg sender plain_msg) /\      
            get_label plain_msg `can_flow tr` (join (principal_label sender) (principal_label receiver))
          )
        ) else (
          event_triggered tr sender (CommAuthSendMsg sender payload)
        )
      ));
    sign_message_proof tr sender receiver enc_payload true sk_sender sign_nonce;
    ()
  );*)
  pk_enc_extract_msg_enc_lemma pk_receiver enc_nonce payload enc_payload;
  sign_message_proof tr sender receiver enc_payload true sk_sender sign_nonce;
  ()


val send_confidential_authenticated_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_invariants /\
    comm_layer_preds_later tr (higher_layer_preds.send_conf sender receiver payload) /\
    comm_layer_preds_later tr (higher_layer_preds.send_auth sender payload) /\
    comm_layer_preds_later tr (higher_layer_preds.send_conf_auth sender receiver payload) /\
    has_communication_layer_event_predicates higher_layer_preds /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
  )
  (ensures (
    let (_, tr_out) = send_confidential_authenticated comm_keys_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
let send_confidential_authenticated_proof #invs tr higher_layer_preds comm_keys_ids sender receiver payload =
  match send_confidential_authenticated comm_keys_ids sender receiver payload tr with
  | (None, tr_out) -> ()
  | (Some _, tr_out) -> (
    let (Some pk_receiver, tr) = get_public_key sender comm_keys_ids.pki (LongTermPkEncKey comm_layer_pkenc_tag) receiver tr in
    let (Some sk_sender, tr) = get_private_key  sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) tr in
    let (enc_nonce, tr) = mk_rand PkNonce (long_term_key_label sender) 32 tr in
    let (sign_nonce, tr) = mk_rand SigNonce (long_term_key_label sender) 32 tr in
    let ((), tr) = trigger_event sender (CommConfSendMsg sender receiver payload) tr in
    let ((), tr) = trigger_event sender (CommAuthSendMsg sender payload) tr in
    assert(event_triggered tr sender (CommConfSendMsg sender receiver payload));
    assert(event_triggered tr sender (CommAuthSendMsg sender payload));
    let ((), tr) = trigger_event sender (CommConfAuthSendMsg sender receiver payload) tr in
    assert(event_triggered tr sender (CommConfAuthSendMsg sender receiver payload));
    encrypt_and_sign_message_proof tr sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce;
    let msg = encrypt_and_sign_message sender receiver payload pk_receiver sk_sender enc_nonce sign_nonce in
    let (msg_id, tr) = send_msg msg tr in
    assert(tr_out == tr);
    ()
  )


val verify_and_decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> msg_encrypted_signed:bytes ->
  sk_receiver:bytes -> vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_invariants /\
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
          //event_triggered tr sender (CommAuthSendMsg sender payload) /\        
          //event_triggered tr sender (CommConfSendMsg sender receiver payload) /\
          event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) ///\
          //is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
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
    assert(is_publishable tr enc_payload /\
      (
        (
          sender' == sender /\
          (
            match pk_enc_extract_msg enc_payload with
            | None -> False
            | Some plain_payload -> (
              vk_sender `has_signkey_usage tr` long_term_key_type_to_usage (LongTermSigKey comm_layer_sign_tag) sender /\     
              get_label tr enc_payload `can_flow tr` public /\
              event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
            )
          )
        ) \/ (
          is_corrupt tr (long_term_key_label sender)
          //get_label vk_sender `can_flow tr` public
        )
      )
    );

    decrypt_message_proof tr receiver sk_receiver enc_payload;
    let Some payload' = decrypt_message sk_receiver enc_payload in
    
    //assert(pk_enc_extract_pk enc_payload == Some (DY.Core.Bytes.Type.Pk sk_receiver));
    assert(payload == payload');
    assert(exists sender.
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
      (       
        event_triggered tr sender (CommConfSendMsg sender receiver payload) \/
        is_publishable tr payload
      )
    );
    assert(exists sender. is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload);

    assert(is_knowable_by (principal_label receiver) tr payload);
  
    pk_enc_extract_msg_dec_lemma sk_receiver enc_payload payload;
    assert(
      match pk_enc_extract_msg enc_payload with
      | Some plain_payload -> (
        payload == plain_payload /\
        event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
       
      ) \/
      is_corrupt tr (long_term_key_label sender));

    ()
    (*introduce ~(is_corrupt tr (principal_label sender)) /\ ~(is_publishable tr payload) ==> event_triggered tr sender (CommConfSendMsg sender receiver payload)
    with _. (
      assert(exists payload. event_triggered tr sender (CommConfSendMsg sender receiver payload));
      eliminate exists plain_msg. event_triggered tr sender (CommConfSendMsg sender receiver plain_msg)
      returns event_triggered tr sender (CommConfSendMsg sender receiver payload)
      with _. (
        assert(
          event_triggered tr sender (CommAuthSendMsg sender payload) /\
          is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
          event_triggered tr sender (CommConfSendMsg sender receiver payload)
        );
        ()
      )
    )*)
    (*reveal_opaque (`%pk_enc) (pk_enc);
    reveal_opaque (`%pk_dec) (pk_dec);
    let DY.Core.Bytes.Type.PkEnc pk nonce msg = enc_payload in
    assert(if_comm_conf_payload sender receiver'' enc_payload tr \/
      is_corrupt tr (principal_label sender));
    assert(get_usage sk_receiver == PkKey comm_layer_pkenc_tag empty);
    assert(Pk sk_receiver == pk);
    reveal_opaque (`%get_sk_usage) (get_sk_usage);
    assert(get_sk_usage pk == PkKey comm_layer_pkenc_tag empty);
    assert(
      (
        get_sk_label pk == principal_label receiver'' /\
        event_triggered tr sender (CommConfSendMsg sender receiver'' msg)
      ) \/
        is_corrupt tr (principal_label sender)                                                        
    );
    assert(get_label sk_receiver == principal_label receiver);
    assert(get_sk_label pk == principal_label receiver'' \/
      is_corrupt tr (principal_label sender));
    reveal_opaque (`%get_sk_label) (get_sk_label);
    assert(receiver == receiver'' \/
      is_corrupt tr (principal_label sender));
    decrypt_message_proof tr receiver sk_receiver enc_payload;*)
  )

val receive_confidential_authenticated_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_invariants /\
    has_communication_layer_event_predicates higher_layer_preds
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
let receive_confidential_authenticated_proof #invs tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_confidential_authenticated comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some {sender; receiver=receiver'; payload}, tr_out) -> (
    let (Some msg_encrypted_signed, tr) = recv_msg msg_id tr in
    let Some msg_sig = parse_sig_message msg_encrypted_signed in
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (LongTermPkEncKey comm_layer_pkenc_tag) tr in
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) msg_sig.sender tr in
    let Some msg = verify_and_decrypt_message receiver msg_encrypted_signed sk_receiver vk_sender in
    verify_and_decrypt_message_proof tr sender receiver msg_encrypted_signed sk_receiver vk_sender;
    assert(event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) \/
      is_corrupt tr (long_term_key_label sender));
    assert(is_knowable_by (join (principal_label sender) (principal_label receiver)) tr msg.payload \/
      is_corrupt tr (long_term_key_label sender));
    let ((), tr) = trigger_event receiver (CommConfAuthReceiveMsg msg.sender receiver msg.payload) tr in
    assert(event_triggered tr receiver (CommConfAuthReceiveMsg msg.sender receiver msg.payload));
    assert(trace_invariant tr);
    assert(tr == tr_out);
    ()
  )