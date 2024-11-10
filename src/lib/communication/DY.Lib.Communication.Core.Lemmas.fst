module DY.Lib.Communication.Core.Lemmas

open Comparse
open DY.Core
open DY.Lib.Communication.Core.Extension
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed

open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants

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
    is_secret (long_term_key_label sender) tr nonce /\
    nonce `has_usage tr` PkNonce /\
    is_public_key_for tr pk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
    event_triggered tr sender (CommConfSendMsg sender receiver payload)
  )
  (ensures
    is_publishable tr (encrypt_message pk_receiver nonce payload)
  )
let encrypt_message_proof #cinvs tr sender receiver pk_receiver nonce pkenc_in = ()

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
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates higher_layer_preds /\
    higher_layer_preds.send_conf tr sender receiver payload /\
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
    has_communication_layer_crypto_predicates /\
    is_private_key_for tr sk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    bytes_invariant tr msg_encrypted
  )
  (ensures
    (
      match decrypt_message sk_receiver msg_encrypted with
      | None -> True
      | Some payload -> (exists sender.
        is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
        (
          event_triggered tr sender (CommConfSendMsg sender receiver payload) \/
          is_publishable tr payload
        )
      )
    )    
  )
let decrypt_message_proof #cinvs tr receiver sk_receiver msg_encrypted =
  match decrypt_message sk_receiver msg_encrypted with
  | None -> ()
  | Some payload -> ()

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
    has_communication_layer_crypto_predicates /\
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
  sender:principal -> receiver:principal -> payload:bytes -> pk_receiver:bytes ->
  is_encrypted:bool -> sk_sender:bytes -> nonce:bytes -> 
  Lemma
  (requires
    has_communication_layer_invariants /\
    is_secret (long_term_key_label sender) tr nonce /\
    nonce `has_usage tr` SigNonce /\
    is_private_key_for tr sk_sender (LongTermSigKey comm_layer_sign_tag) sender /\
    is_publishable tr payload /\
    is_publishable tr pk_receiver /\
    (
      if is_encrypted then (
        (exists plain_payload nonce.
          //pk_enc_extract_pk payload == Some (DY.Core.Bytes.Type.Pk sk_receiver) /\
          //Some plain_msg == pk_dec sk_receiver payload /\
          payload == encrypt_message pk_receiver nonce plain_payload /\
          
          //bytes_well_formed tr pk_receiver /\
          //pk_receiver `has_sk_usage tr` (long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag) plain_msg.receiver) /\
          //get_label sk_receiver == principal_label receiver /\
          //event_triggered tr sender (CommConfSendMsg sender receiver plain_msg) /\
          event_triggered tr sender (CommAuthSendMsg sender plain_payload) /\ 
          event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload) //\   
          //get_label tr plain_msg.payload `can_flow tr` (join (principal_label plain_msg.sender) (principal_label plain_msg.receiver))
        )
      ) else (
        event_triggered tr sender (CommAuthSendMsg sender payload)
      )
    )
  )
  (ensures
    is_publishable tr (sign_message sender receiver payload pk_receiver is_encrypted sk_sender nonce)
  )
let sign_message_proof #cinvs tr sender receiver payload pk_receiver is_encrypted sk_sender nonce =
  let msg:communication_message = {sender; receiver; payload} in
  if is_encrypted then (
    let sig_input = Encrypted pk_receiver msg in
    let sig_input_bytes = serialize signature_input sig_input in
    assert(is_publishable tr payload);
    assert(is_publishable tr pk_receiver);
    serialize_wf_lemma signature_input (is_publishable tr) sig_input;
    let signature = sign sk_sender nonce sig_input_bytes in
    let msg_signed = {msg=sig_input_bytes; signature} in
    assert(bytes_invariant tr signature);
    serialize_wf_lemma communication_message_sign (is_publishable tr) msg_signed;
    ()
  ) else (
    let sig_input = Plain {sender; receiver; payload} in
    let sig_input_bytes = serialize signature_input sig_input in
    serialize_wf_lemma signature_input (is_publishable tr) sig_input;
    assert(is_publishable tr sig_input_bytes);
    let signature = sign sk_sender nonce sig_input_bytes in
    assert(bytes_invariant tr signature);
    let msg_signed = {msg=sig_input_bytes; signature} in
    //assert(is_publishable tr sig_input_bytes);
    //assert(get_label tr signature `can_flow tr` public);
    //assert(is_publishable tr signature);
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
    trace_invariant tr /\ 
    has_private_keys_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates higher_layer_preds /\
    higher_layer_preds.send_auth tr sender payload /\
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

#push-options "--fuel 0 --ifuel 1 --z3rlimit 20"
val verify_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal ->
  msg_bytes:bytes ->
  vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_publishable tr msg_bytes /\
    is_public_key_for tr vk_sender (LongTermSigKey comm_layer_sign_tag) sender
  )
  (ensures (
    match verify_message receiver msg_bytes vk_sender with
    | Some cm -> (
      is_publishable tr cm.payload /\
      
      (
        cm.sender == sender /\
        cm.receiver == receiver /\
        (
          let Some msg_signed = parse communication_message_sign msg_bytes in
          let Some sign_input = parse signature_input msg_signed.msg in
          match sign_input with
          | Plain cm' -> (
            is_publishable tr cm.payload /\
            event_triggered tr sender (CommAuthSendMsg sender cm.payload)
          )
          | Encrypted pk_receiver cm' -> (
            exists plain_payload nonce.
              cm.payload == encrypt_message pk_receiver nonce plain_payload /\
              event_triggered tr sender (CommAuthSendMsg sender plain_payload) /\
              event_triggered tr cm.sender (CommConfAuthSendMsg cm.sender cm.receiver plain_payload)
          )
        ) \/ (
          is_corrupt tr (long_term_key_label sender)
        )
      )
    )
    | _ -> True
  ))
let verify_message_proof #cinvs tr sender receiver msg_bytes vk_sender =
  assert(get_signkey_label tr vk_sender == long_term_key_label sender);
  match verify_message receiver msg_bytes vk_sender with
  | Some cm -> (
    assert(is_publishable tr msg_bytes);
    parse_wf_lemma communication_message_sign (is_publishable tr) msg_bytes;
    let Some msg_signed = parse communication_message_sign msg_bytes in
    assert(is_publishable tr msg_signed.msg);
    parse_wf_lemma signature_input (is_publishable tr) msg_signed.msg;
    let Some sign_input = parse signature_input msg_signed.msg in
    assert(is_publishable tr cm.payload);

    //assert(bytes_invariant tr vk_sender);
    //assert(bytes_invariant tr msg_bytes);
    //assert(bytes_invariant tr msg_signed.signature);
    

    (*assert(event_triggered tr sender (CommAuthSendMsg sender payload) \/
      get_signkey_label vk_sender `can_flow tr` public);
    
    let DY.Core.Bytes.Type.Sign sk nonce sig_input_bytes = msg_signed.signature in
    assert(sign_pred.pred tr (Vk sk) sig_input_bytes \/
      get_signkey_label vk_sender `can_flow tr` public);

    assert(receiver == receiver');
    assert(sender == sender' \/
      get_signkey_label vk_sender `can_flow tr` public);*)
    
    match sign_input with
    | Plain cm' -> (
      //let sig_input_p = Plain {sender=sender'; receiver=msg_signed.receiver; payload=msg_signed.payload} in
      //let Some sig_input = parse signature_input msg_signed.payload in
      //FStar.Classical.move_requires (serialize_wf_lemma signature_input (is_publishable tr)) sign_input;
      assert(cm.payload == cm'.payload);
      assert(event_triggered tr sender (CommAuthSendMsg sender cm.payload) \/
        is_corrupt tr (long_term_key_label sender));
      ()
    )
    | Encrypted pk_receiver cm' -> (
      //let sig_input_e = Encrypted msg_signed.payload in
      //let sig_input_bytes_e = serialize signature_input #parseable_serializeable_bytes_signature_input sig_input_e in
      //serialize_wf_lemma signature_input (is_publishable tr) sign_input;
      assert(bytes_invariant tr msg_signed.signature);
      
      assert(
        (exists plain_payload nonce.
          cm.payload == encrypt_message pk_receiver nonce plain_payload) \/
          is_corrupt tr (long_term_key_label sender)
      );

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
    )  
  )
  | _ -> ()
#pop-options

val receive_authenticated_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\ 
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates higher_layer_preds
  )
  (ensures (
    match receive_authenticated comm_keys_ids receiver msg_id tr with
    | (Some cm, tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommAuthReceiveMsg cm.sender receiver cm.payload)
    )
  ))
let receive_authenticated_proof #invs tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_authenticated comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some cm', tr_out) -> (
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
  let enc_payload = encrypt_message pk_receiver enc_nonce payload in
  let msg_signed = sign_message sender receiver enc_payload pk_receiver true sk_sender sign_nonce in
  
  encrypt_message_proof tr sender receiver pk_receiver enc_nonce payload;
  sign_message_proof tr sender receiver enc_payload pk_receiver true sk_sender sign_nonce;

  

  assert(get_label tr sk_sender == long_term_key_label sender);
  assert(is_publishable tr enc_payload);
  assert(enc_payload == encrypt_message pk_receiver enc_nonce payload);
  assert(event_triggered tr sender (CommConfSendMsg sender receiver payload));
  assert(event_triggered tr sender (CommAuthSendMsg sender payload));
  assert(event_triggered tr sender (CommConfAuthSendMsg sender receiver payload));
  ()
  

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
  
  

#push-options "--z3rlimit 10"
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
    has_communication_layer_crypto_predicates /\
    has_communication_layer_event_predicates higher_layer_preds /\
    higher_layer_preds.send_conf tr sender receiver payload /\
    higher_layer_preds.send_conf_auth tr sender receiver payload /\
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
    let (Some pk_receiver, tr') = get_public_key sender comm_keys_ids.pki (LongTermPkEncKey comm_layer_pkenc_tag) receiver tr in
    let (Some sk_sender, tr') = get_private_key  sender comm_keys_ids.private_keys (LongTermSigKey comm_layer_sign_tag) tr' in
    let (enc_nonce, tr') = mk_rand PkNonce (long_term_key_label sender) 32 tr' in
    let (sign_nonce, tr') = mk_rand SigNonce (long_term_key_label sender) 32 tr' in
    
    higher_layer_preds.send_conf_later tr tr' sender receiver payload;
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


#push-options "--fuel 4 --ifuel 4 --z3rlimit 50"
val verify_and_decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> msg_encrypted_signed:bytes ->
  sk_receiver:bytes -> vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_publishable tr msg_encrypted_signed /\
    is_private_key_for tr sk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    is_public_key_for tr vk_sender (LongTermSigKey comm_layer_sign_tag) sender /\
    Some sender == get_sender msg_encrypted_signed
  )
  (ensures (
    match verify_and_decrypt_message receiver sk_receiver vk_sender msg_encrypted_signed with
    | None -> True
    | Some cm -> (
      is_knowable_by (principal_label receiver) tr cm.payload /\
      (
        (
          //event_triggered tr sender (CommAuthSendMsg sender payload) /\        
          //event_triggered tr sender (CommConfSendMsg sender receiver payload) /\
          event_triggered tr sender (CommConfAuthSendMsg sender receiver cm.payload) ///\
          //is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
        ) \/ (
          is_corrupt tr (long_term_key_label sender)
        )
      )
    )
  ))
let verify_and_decrypt_message_proof #cinvs tr sender receiver msg_encrypted_signed sk_receiver vk_sender =
  match verify_and_decrypt_message receiver sk_receiver vk_sender msg_encrypted_signed with
  | None -> ()
  | Some cm -> (
    verify_message_proof tr sender receiver msg_encrypted_signed vk_sender;
    let Some cm' = verify_message receiver msg_encrypted_signed vk_sender in    

    let Some msg_signed = parse communication_message_sign msg_encrypted_signed in
    let Some sign_input = parse signature_input msg_signed.msg in
    assert(Encrypted? sign_input);
    assert((Encrypted?.pk sign_input) = pk sk_receiver);
    let Encrypted pk_receiver cm'' = sign_input in
    assert(
      (exists plain_payload nonce.
        cm'.payload == encrypt_message pk_receiver nonce plain_payload /\
        event_triggered tr sender (CommAuthSendMsg sender plain_payload) /\
        event_triggered tr cm.sender (CommConfAuthSendMsg cm.sender cm.receiver plain_payload)) \/
      is_corrupt tr (long_term_key_label sender)
    );
    introduce (~(is_corrupt tr (long_term_key_label sender))) ==> 
    (exists plain_payload nonce.
        cm'.payload == encrypt_message pk_receiver nonce plain_payload /\
        event_triggered tr sender (CommAuthSendMsg sender plain_payload) /\
        event_triggered tr sender (CommConfAuthSendMsg sender receiver cm.payload)
    )
    with _. (
      eliminate exists plain_payload nonce.
          cm'.payload == encrypt_message pk_receiver nonce plain_payload /\
          event_triggered tr sender (CommAuthSendMsg sender plain_payload) /\
          event_triggered tr cm.sender (CommConfAuthSendMsg cm.sender cm.receiver plain_payload)
      returns (event_triggered tr sender (CommConfAuthSendMsg sender receiver cm.payload)
      )
      with _. (
        pk_dec_enc sk_receiver nonce plain_payload;
        assert(cm'.payload == pk_enc pk_receiver nonce plain_payload);
        
        assert(event_triggered tr sender (CommConfAuthSendMsg sender receiver cm.payload));
            
        assert(Some cm.payload == pk_dec sk_receiver cm'.payload);
        assert(Some cm.payload == pk_dec sk_receiver (pk_enc pk_receiver nonce cm.payload));
        
        
        assert(cm'.payload == encrypt_message pk_receiver nonce plain_payload);
        assert(decrypt_message sk_receiver cm'.payload == Some plain_payload);
        
        assert(plain_payload == cm.payload);
        
        ()
      )
    )
    (*assert(is_publishable tr msg_encrypted_signed);
    parse_wf_lemma communication_message_sign (is_publishable tr) msg_encrypted_signed;
    //parse_wf_lemma communication_message_sign (bytes_invariant tr) msg_encrypted_signed;
    let Some signed_msg = parse communication_message_sign msg_encrypted_signed in
    assert(is_publishable tr signed_msg.payload);
    parse_wf_lemma signature_input (is_publishable tr) signed_msg.payload;
    let Some signature_in = parse signature_input signed_msg.payload in
    let enc_payload = Encrypted?.payload signature_in in
    assert(is_publishable tr enc_payload);
    decrypt_message_proof tr receiver sk_receiver enc_payload;
    let Some (PkEncSignInput cm) = decrypt_message sk_receiver enc_payload in
    assert(bytes_invariant tr cm.payload);
    assert(cm.receiver == receiver);
    assert(event_triggered tr cm.sender (CommConfAuthSendMsg cm.sender cm.receiver cm.payload) \/
      get_label tr cm.payload `can_flow tr` public);
    ()
    *)
    (*
    verify_message_proof tr sender receiver msg_encrypted_signed true vk_sender;
    let Some {sender=sender''; receiver=receiver''; payload=enc_payload} = verify_message receiver msg_encrypted_signed true vk_sender in    
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

    // TODO transfer this property into the event or separate from the event
    assert(is_knowable_by (principal_label receiver) tr payload);
      
    ()
    *)
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
    (*
    let DY.Core.Bytes.Type.PkEnc pk nonce msg = enc_payload in
    assert(if_comm_conf_payload sender receiver'' enc_payload tr \/
      is_corrupt tr (principal_label sender));
    assert(get_usage sk_receiver == PkKey comm_layer_pkenc_tag empty);
    assert(Pk sk_receiver == pk);
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
    assert(receiver == receiver'' \/
      is_corrupt tr (principal_label sender));
    decrypt_message_proof tr receiver sk_receiver enc_payload;*)
  )

//#push-options "--fuel 4 --ifuel 4 --z3rlimit 50"
(*val combine_lemma:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal ->
  payload:bytes -> enc_payload:bytes ->
  sk_receiver:bytes -> pk_receiver:bytes ->
  Lemma
  (requires
    has_communication_layer_invariants /\
    is_publishable tr enc_payload /\
    bytes_invariant tr payload /\
    is_private_key_for tr sk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver /\
    (
      (exists (plain_payload:communication_message) nonce.
        enc_payload == encrypt_message pk_receiver nonce (PkEncSignInput plain_payload) /\
        plain_payload.sender == sender /\
        event_triggered tr sender (CommConfAuthSendMsg sender plain_payload.receiver plain_payload.payload)
        //(pk sk_receiver) == pk_receiver
      ) \/
      is_corrupt tr (long_term_key_label sender)
    ) /\ (
      (
        event_triggered tr sender (CommConfSendMsg sender receiver payload) /\
        event_triggered tr sender (CommConfAuthSendMsg sender receiver payload)
      ) \/ (
        is_publishable tr payload
      )
    ) /\ (
      let sign_input_bytes = serialize signature_input #parseable_serializeable_bytes_signature_input (Encrypted pk_receiver enc_payload) in
      let signed_msg_bytes = serialize communication_message_sign #parseable_serializeable_bytes_communication_message_sign {payload=sign_input_bytes; signature=empty} in
      Some {sender; receiver; payload} = decrypt_signed_message receiver sk_receiver signed_msg_bytes
    )
  )
  (ensures
    event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) \/
    is_corrupt tr (long_term_key_label sender) 
  )
let combine_lemma #invs tr sender receiver payload enc_payload sk_receiver pk_receiver =
  assert(forall (plain_payload:communication_message).
    let pkenc_in_bytes = serialize pkenc_input (PkEncSignInput plain_payload) in
    (pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag) receiver) pkenc_in_bytes ==>
      event_triggered tr plain_payload.sender (CommConfAuthSendMsg plain_payload.sender receiver plain_payload.payload))
  );
  
  assert(
    (exists (plain_payload:communication_message) nonce.
        enc_payload == encrypt_message pk_receiver nonce (PkEncSignInput plain_payload) /\
        //decrypt_message sk_receiver enc_payload == Some (PkEncSignInput plain_payload) /\
        plain_payload.sender == sender /\
        //plain_payload.receiver == receiver /\
        //plain_payload.payload == payload /\
        event_triggered tr sender (CommConfAuthSendMsg sender plain_payload.receiver plain_payload.payload)
        //(pk sk_receiver) == pk_receiver
      ) \/
      is_corrupt tr (long_term_key_label sender)
  );

  introduce (~(is_corrupt tr (long_term_key_label sender))) ==> 
    (exists (plain_payload:communication_message) nonce. 
      enc_payload == encrypt_message pk_receiver nonce (PkEncSignInput plain_payload) /\
      plain_payload.sender == sender /\
      event_triggered tr sender (CommConfAuthSendMsg sender receiver payload)
      //(pk sk_receiver) == pk_receiver
    )
  with _. (
    eliminate exists (plain_payload:communication_message) nonce. 
      enc_payload == encrypt_message pk_receiver nonce (PkEncSignInput plain_payload) /\
      plain_payload.sender == sender /\
      event_triggered tr sender (CommConfAuthSendMsg sender plain_payload.receiver plain_payload.payload)
      //(pk sk_receiver) == pk_receiver
    returns (event_triggered tr sender (CommConfAuthSendMsg sender receiver payload)
    )
    with _. (
      pk_dec_enc sk_receiver nonce (serialize pkenc_input (PkEncSignInput plain_payload));
      let pkenc_in_bytes = serialize pkenc_input #parseable_serializeable_bytes_pkenc_input (PkEncSignInput plain_payload) in
      assert(enc_payload == pk_enc pk_receiver nonce pkenc_in_bytes);
      
      (*
      The following code needs this precondition:
      is_private_key_for tr sk_receiver (LongTermPkEncKey comm_layer_pkenc_tag) receiver

      assert(sk_receiver `has_usage tr` (long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag) receiver));
     
      assert(decrypt_message sk_receiver enc_payload == Some (PkEncSignInput {sender; receiver; payload}));
      
      let b = serialize pkenc_input #parseable_serializeable_bytes_pkenc_input (PkEncSignInput {sender; receiver; payload}) in
      assert(bytes_invariant tr payload);
      serialize_wf_lemma pkenc_input (bytes_invariant tr) (PkEncSignInput {sender; receiver; payload});
      assert(bytes_invariant tr b);
      assert(bytes_invariant tr enc_payload);
      parse_wf_lemma pkenc_input (bytes_invariant tr) enc_payload;
      
      let Some b' = pk_dec sk_receiver enc_payload in
      assert(parse pkenc_input b' == Some (PkEncSignInput {sender; receiver; payload}));
      assert(
        pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag) receiver) b' \/
        is_publishable tr b'  
      );
      assert(
        (        
          event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) /\
          is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
        ) \/
        is_publishable tr b'
      );
      assert(plain_payload.sender == sender);
      assert(event_triggered tr sender (CommConfAuthSendMsg sender plain_payload.receiver plain_payload.payload));
      //assert(plain_payload.payload == payload);*)

      
      assert(event_triggered tr sender (CommConfAuthSendMsg sender receiver payload));
      
      
      assert(Some pkenc_in_bytes == pk_dec sk_receiver enc_payload);
      assert(Some pkenc_in_bytes == pk_dec sk_receiver (pk_enc pk_receiver nonce pkenc_in_bytes));
      
      
      assert(enc_payload == encrypt_message pk_receiver nonce (PkEncSignInput plain_payload));
      assert(decrypt_message sk_receiver enc_payload == Some (PkEncSignInput plain_payload));
      
      assert(plain_payload.sender == sender);
      assert(plain_payload.receiver == receiver);
      assert(plain_payload.payload == payload);
      
      
      ()
    )
  );
 ()
  
  (*assert(
    exists payload.
      Some payload == pk_dec sk_receiver (pk_enc (pk sk_receiver) nonce payload)
  );
  assert(
    (exists (plain_payload:communication_message) pk_receiver.
      let pkenc_in_bytes = serialize pkenc_input #parseable_serializeable_bytes_pkenc_input (PkEncSignInput plain_payload) in

      (pk sk_receiver) == pk_receiver /\

      //Some pkenc_in_bytes == pk_dec sk_receiver (pk_enc pk_receiver nonce pkenc_in_bytes) ///\

      enc_payload == pk_enc pk_receiver nonce pkenc_in_bytes /\
      Some pkenc_in_bytes == pk_dec sk_receiver enc_payload //\
      //decrypt_message sk_receiver enc_payload == Some (PkEncSignInput plain_payload) /\
      //plain_payload.sender == sender /\
      //plain_payload.receiver == receiver /\
      //plain_payload.payload == payload /\
      //event_triggered tr sender (CommConfAuthSendMsg sender plain_payload.receiver plain_payload.payload)
    ) \/
    is_corrupt tr (long_term_key_label sender)
  );

  
  assert(Some (PkEncSignInput {sender; receiver; payload}) == decrypt_message sk_receiver enc_payload);
  let Some plain_payload = pk_dec sk_receiver enc_payload in
  FStar.Classical.move_requires (parse_wf_lemma pkenc_input (is_publishable tr)) plain_payload;
  FStar.Classical.move_requires (parse_wf_lemma pkenc_input (bytes_invariant tr)) plain_payload;
  assert(
    (pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag) receiver) plain_payload \/
      is_publishable tr plain_payload    
    ) /\
    (
      (        
        event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) /\
        is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
      ) \/
      is_publishable tr payload
    ) /\
    Some (PkEncSignInput {sender; receiver; payload}) == parse pkenc_input plain_payload
  );

  ()*)*)

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
    has_communication_layer_crypto_predicates /\
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
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (LongTermPkEncKey comm_layer_pkenc_tag) tr in
    let Some sender = get_sender msg_encrypted_signed in
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (LongTermSigKey comm_layer_sign_tag) sender tr in
    verify_and_decrypt_message_proof tr sender receiver msg_encrypted_signed sk_receiver vk_sender;
    let Some cm = verify_and_decrypt_message receiver sk_receiver vk_sender msg_encrypted_signed in
    let ((), tr) = trigger_event receiver (CommConfAuthReceiveMsg cm.sender receiver cm.payload) tr in
    assert(event_triggered tr receiver (CommConfAuthReceiveMsg cm.sender receiver cm.payload));
    assert(trace_invariant tr);
    assert(tr == tr_out);
    ()
  )
#pop-options
