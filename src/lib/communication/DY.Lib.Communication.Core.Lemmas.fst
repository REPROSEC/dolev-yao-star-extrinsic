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
    encrypt_message_proof tr sender receiver pk_receiver nonce payload;
    let msg_encrypted = encrypt_message pk_receiver nonce payload in
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
          payload == encrypt_message pk_receiver nonce plain_payload /\
          event_triggered tr sender (CommAuthSendMsg sender plain_payload) /\ 
          event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
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
    let signature = sign sk_sender nonce sig_input_bytes in
    assert(bytes_invariant tr signature);
    let msg_signed = {msg=sig_input_bytes; signature} in
    assert(bytes_invariant tr signature);
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
  msg_bytes:bytes -> is_encrypted:bool -> sk_receiver:bytes ->
  vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_crypto_predicates /\
    is_publishable tr msg_bytes /\
    is_public_key_for tr vk_sender (LongTermSigKey comm_layer_sign_tag) sender
  )
  (ensures (
    match verify_message receiver msg_bytes is_encrypted sk_receiver vk_sender with
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
let verify_message_proof #cinvs tr sender receiver msg_bytes is_encrypted sk_receiver vk_sender =
  assert(get_signkey_label tr vk_sender == long_term_key_label sender);
  match verify_message receiver msg_bytes is_encrypted sk_receiver vk_sender with
  | Some cm -> (
    parse_wf_lemma communication_message_sign (is_publishable tr) msg_bytes;
    let Some msg_signed = parse communication_message_sign msg_bytes in
    parse_wf_lemma signature_input (is_publishable tr) msg_signed.msg;
    ()
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
  sign_message_proof tr sender receiver enc_payload pk_receiver true sk_sender sign_nonce;
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
    is_public_key_for tr vk_sender (LongTermSigKey comm_layer_sign_tag) sender
  )
  (ensures (
    match verify_and_decrypt_message receiver sk_receiver vk_sender msg_encrypted_signed with
    | None -> True
    | Some cm -> (
      is_knowable_by (principal_label receiver) tr cm.payload /\
      (
        (
          event_triggered tr sender (CommAuthSendMsg sender cm.payload) /\
          event_triggered tr sender (CommConfAuthSendMsg sender receiver cm.payload)
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
    verify_message_proof tr sender receiver msg_encrypted_signed true sk_receiver vk_sender;
    let Some cm' = verify_message receiver msg_encrypted_signed true sk_receiver vk_sender in    

    let Some msg_signed = parse communication_message_sign msg_encrypted_signed in
    let Some sign_input = parse signature_input msg_signed.msg in
    let Encrypted pk_receiver _ = sign_input in
    assert(pk_receiver == pk sk_receiver);
    
    introduce (~(is_corrupt tr (long_term_key_label sender))) ==>  (
        event_triggered tr sender (CommAuthSendMsg sender cm.payload) /\
        event_triggered tr sender (CommConfAuthSendMsg sender receiver cm.payload)
      )
    with _. (
      eliminate exists plain_payload nonce.
          cm'.payload == encrypt_message pk_receiver nonce plain_payload /\
          event_triggered tr sender (CommAuthSendMsg sender plain_payload) /\
          event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
      returns (event_triggered tr sender (CommAuthSendMsg sender cm.payload) /\
        event_triggered tr sender (CommConfAuthSendMsg sender receiver cm.payload)
      )
      with _. (
        pk_dec_enc sk_receiver nonce plain_payload;
        ()
      )
    )
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
