module DY.Lib.Communication.API.Lemmas

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed

open DY.Lib.Communication.API.Predicates
open DY.Lib.Communication.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(**** Confidential Send and Receive Lemmas ****)

val encrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> payload:bytes ->
  pk:bytes -> nonce:bytes ->
  Lemma
  (requires
    has_communication_layer_invariants cinvs /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
    is_secret (principal_label sender) tr nonce /\
    PkNonce? (get_usage nonce) /\
    is_encryption_key (PkKey comm_layer_pkenc_tag empty) (principal_label receiver) tr pk /\
    event_triggered tr sender (CommConfSendMsg sender receiver payload)
  )
  (ensures
    is_publishable tr (encrypt_message sender receiver payload pk nonce)
  )
let encrypt_message_proof #cinvs tr sender receiver payload pk nonce =
  let msg = CM {sender; receiver; payload} in  
  serialize_wf_lemma communication_message (is_knowable_by (join (principal_label sender) (principal_label receiver)) tr) msg;
  ()

val send_confidential_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  keys_sess_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant invs /\
    has_communication_layer_invariants invs.crypto_invs /\
    (forall tr'.
      tr <$ tr' ==> higher_layer_preds.send_conf tr' sender receiver payload) /\
    has_communication_layer_event_predicates invs higher_layer_preds /\    
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
    let (Some pk_receiver, tr) = get_public_key sender keys_sess_ids.pki (PkEnc comm_layer_pkenc_tag) receiver tr in
    let (nonce, tr) = mk_rand PkNonce (principal_label sender) 32 tr in
    let ((), tr) = trigger_event sender (CommConfSendMsg sender receiver payload) tr in
    let msg_encrypted = encrypt_message sender receiver payload pk_receiver nonce in
    assert(higher_layer_preds.send_conf tr sender receiver payload);
    assert(event_triggered tr sender (CommConfSendMsg sender receiver payload));
    encrypt_message_proof tr sender receiver payload pk_receiver nonce;
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
    has_communication_layer_invariants cinvs /\
    is_decryption_key (PkKey comm_layer_pkenc_tag empty) (principal_label receiver) tr sk_receiver /\
    bytes_invariant tr msg_encrypted
  )
  (ensures (
    match decrypt_message sk_receiver msg_encrypted with
    | Some {sender; receiver=receiver'; payload} -> (
      let Some msg_plain = pk_dec sk_receiver msg_encrypted in
      (is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
        event_triggered tr sender (CommConfSendMsg sender receiver payload)) \/
        is_publishable tr payload
    )
    | _ -> True
  ))
let decrypt_message_proof #cinvs tr receiver sk_receiver msg_encrypted =
  match decrypt_message sk_receiver msg_encrypted with
  | Some {sender; receiver=receiver'; payload} -> ( 
    let Some msg_plain = pk_dec sk_receiver msg_encrypted in
    FStar.Classical.move_requires (parse_wf_lemma communication_message (is_publishable tr)) msg_plain;
    FStar.Classical.move_requires (parse_wf_lemma communication_message (bytes_invariant tr)) msg_plain;
    ()
  )
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
    has_private_keys_invariant invs /\
    has_communication_layer_invariants invs.crypto_invs /\
    (
      match receive_confidential comm_keys_ids receiver msg_id tr with
      | (None, tr_out) -> True
      | (Some {sender; receiver=receiver'; payload}, tr_out) -> 
        (forall tr'. tr <$ tr' ==> higher_layer_preds.receive_conf tr' sender receiver payload)
    ) /\
    has_communication_layer_event_predicates invs higher_layer_preds
  )
  (ensures (
    match receive_confidential comm_keys_ids receiver msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some {sender; receiver=receiver'; payload}, tr_out) -> ( 
      trace_invariant tr_out /\
      event_triggered tr_out receiver (CommConfReceiveMsg sender receiver payload)
    )
  ))
let receive_confidential_proof #invs tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_confidential comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some {sender; receiver=receiver'; payload}, tr_out) -> (
    let (Some sk_receiver, tr) = get_private_key receiver comm_keys_ids.private_keys (PkDec comm_layer_pkenc_tag) tr in
    let (Some msg_encrypted, tr) = recv_msg msg_id tr in
    let Some msg_plain = decrypt_message sk_receiver msg_encrypted in
    decrypt_message_proof tr receiver sk_receiver msg_encrypted;
    let ((), tr) = trigger_event receiver (CommConfReceiveMsg msg_plain.sender receiver msg_plain.payload) tr in
    assert(tr_out == tr);
    ()
  )


(**** Authenticated Send and Receive Lemmas ****)

val sign_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> payload:bytes ->
  sk:bytes -> nonce:bytes ->
  Lemma
  (requires
    has_communication_layer_invariants cinvs /\
    is_publishable tr payload /\
    is_secret (principal_label sender) tr nonce /\
    SigNonce? (get_usage nonce) /\
    is_signature_key (SigKey comm_layer_sign_tag empty) (principal_label sender) tr sk /\
    event_triggered tr sender (CommAuthSendMsg sender payload)
  )
  (ensures
    is_publishable tr (sign_message sender receiver payload sk nonce)
  )
let sign_message_proof #cinvs tr sender receiver payload sk nonce =
  let msg = CM {sender; receiver; payload} in
  serialize_wf_lemma communication_message (is_publishable tr) msg;
  let msg_bytes = serialize communication_message #parseable_serializeable_bytes_communication_message msg in
  let signature = sign sk nonce msg_bytes in
  let msg_signed = CMSign {sender; receiver; payload; signature} in  
  serialize_wf_lemma communication_message #parseable_serializeable_bytes_communication_message (is_publishable tr) msg_signed;
  ()

val send_authenticated_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\ has_private_keys_invariant invs /\
    has_communication_layer_invariants invs.crypto_invs /\
    (forall tr'. tr <$ tr' ==> higher_layer_preds.send_auth tr' sender payload) /\
    has_communication_layer_event_predicates invs higher_layer_preds /\
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
      let (Some sk_sender, tr) = get_private_key sender comm_keys_ids.private_keys (Sign comm_layer_sign_tag) tr in
      let (nonce,  tr) = mk_rand SigNonce (principal_label sender) 32 tr in      
      let ((), tr) = trigger_event sender (CommAuthSendMsg sender payload) tr in
      assert(event_triggered tr sender (CommAuthSendMsg sender payload)); 
      let msg_signed = sign_message sender receiver payload sk_sender nonce in
      sign_message_proof tr sender receiver payload sk_sender nonce;
      let (msg_id, tr) = send_msg msg_signed tr in
      assert(tr_out == tr);
      ()
    )
  

#push-options "--ifuel 1 --fuel 0"
val verify_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal ->
  msg_bytes:bytes -> vk_sender:bytes ->
  Lemma
  (requires
    has_communication_layer_invariants cinvs /\
    is_publishable tr msg_bytes /\
    is_verification_key (SigKey comm_layer_sign_tag empty) (principal_label sender) tr vk_sender
  )
  (ensures (
    match verify_message receiver msg_bytes vk_sender with
    | Some {sender=sender'; receiver=receiver'; payload} -> (
      is_publishable tr payload /\
      ((get_signkey_label vk_sender == principal_label sender' /\
        sender' == sender /\
        event_triggered tr sender' (CommAuthSendMsg sender' payload)) \/
        get_signkey_label vk_sender `can_flow tr` public)      
    )
    | _ -> True
  ))
let verify_message_proof #cinvs tr sender receiver msg_bytes vk_sender =
  assert(get_signkey_label vk_sender == principal_label sender);
  match verify_message receiver msg_bytes vk_sender with
  | Some {sender=sender'; receiver=receiver'; payload} -> (
    parse_wf_lemma communication_message (is_publishable tr) msg_bytes;
    let msg = CM {sender=sender'; receiver=receiver'; payload} in
    serialize_wf_lemma communication_message #parseable_serializeable_bytes_communication_message (is_publishable tr) msg;
    ()
  )
  | _ -> ()
#pop-options

val extract_data_from_msg_id:
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  (principal -> principal -> bytes -> bytes -> prop) ->
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
        match verify_message receiver msg_signed vk_sender with
        | None -> True
        | Some {sender=sender'; receiver=receiver'; payload} -> (
          fn sender receiver vk_sender payload
        )
      )
    )
  )

val receive_authenticated_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\ has_pki_invariant invs /\
    has_communication_layer_invariants invs.crypto_invs /\
    (
      extract_data_from_msg_id tr comm_keys_ids receiver msg_id (
        fun sender receiver vk_sender payload ->
          (forall tr'. tr <$ tr' ==> higher_layer_preds.receive_auth tr' sender receiver vk_sender payload)
      )
    ) /\
    has_communication_layer_event_predicates invs higher_layer_preds
  )
  (ensures (
    let (_, tr_out) = receive_authenticated comm_keys_ids receiver msg_id tr in
    trace_invariant tr_out /\
    (
      extract_data_from_msg_id tr comm_keys_ids receiver msg_id (
        fun sender receiver vk_sender payload ->
          event_triggered tr_out receiver (CommAuthReceiveMsg sender receiver vk_sender payload)
      )
    )
  ))
let receive_authenticated_proof #invs tr higher_layer_preds comm_keys_ids receiver msg_id =
  match receive_authenticated comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some {sender=sender'; receiver=receiver'; payload}, tr_out) -> (
    let (Some msg_signed, tr) = recv_msg msg_id tr in
    let Some sender = get_sender msg_signed in
    let (Some vk_sender, tr) = get_public_key receiver comm_keys_ids.pki (Verify comm_layer_sign_tag) sender tr in
    let (Some msg_bytes, tr) = recv_msg msg_id tr in
    verify_message_proof tr sender receiver msg_bytes vk_sender;
    ()
  )
