module DY.Lib.Communication

open Comparse
open DY.Core
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Messages ***)

[@@with_bytes bytes]
type communication_message = {
  sender:principal;
  receiver:principal;  
  payload:bytes;
}

%splice [ps_communication_message] (gen_parser (`communication_message))
%splice [ps_communication_message_is_well_formed] (gen_is_well_formed_lemma (`communication_message))

instance parseable_serializeable_bytes_communication_message: parseable_serializeable bytes communication_message
  = mk_parseable_serializeable ps_communication_message

(*** Cryptographic invariants ***)

type higher_layer_pkenc_preds_type = 
  {|crypto_usages|} -> tr:trace -> pk:bytes{PkdecKey? (get_sk_usage pk)} -> msg:bytes ->
    prop

#push-options "--ifuel 2 --fuel 0"
val build_crypto_predicates:
  {|cusa:crypto_usages|} ->
  hlp:higher_layer_pkenc_preds_type{
    forall tr1 tr2 pk msg. 
      hlp tr1 pk msg /\ tr1 <$ tr2 ==>
        hlp tr2 pk msg} ->
  crypto_predicates cusa
let build_crypto_predicates #cusa higher_layer_pkenc_preds = {
  default_crypto_predicates cusa with

  pkenc_pred = (fun tr pk msg ->
    match get_sk_usage pk with
    | PkdecKey "DY.Lib.Communication.PublicKey" -> (
      (match parse communication_message msg with
      | Some {sender; receiver; payload} -> (
        get_sk_label pk == principal_label receiver /\
        (get_label payload) `can_flow tr` (join (principal_label sender) (principal_label receiver))
      )
      | None -> False)
    )
    | _ -> higher_layer_pkenc_preds tr pk msg
  );
  pkenc_pred_later = (fun tr1 tr2 pk msg -> ());
}
#pop-options


type communication_keys_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

val initialize_communication: principal -> principal -> traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
let initialize_communication sender receiver =
  let* client_global_session_priv_key_id = initialize_private_keys sender in
  generate_private_key sender client_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey");*

  let* receiver_global_session_priv_key_id = initialize_private_keys receiver in
  generate_private_key receiver receiver_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey");*

  let*? priv_key_receiver = get_private_key receiver receiver_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey") in
  let pub_key_receiver = pk priv_key_receiver in
  let* client_global_session_pub_key_id = initialize_pki sender in
  install_public_key sender client_global_session_pub_key_id (PkEnc "DY.Lib.Communication.PublicKey") receiver pub_key_receiver;*

  let*? priv_key_client = get_private_key sender client_global_session_priv_key_id (PkDec "DY.Lib.Communication.PublicKey") in
  let pub_key_client = pk priv_key_client in
  let* receiver_global_session_pub_key_id = initialize_pki receiver in
  install_public_key receiver receiver_global_session_pub_key_id (PkEnc "DY.Lib.Communication.PublicKey") sender pub_key_client;*

  let client_comm_keys_sess_ids = {pki=client_global_session_pub_key_id; private_keys=client_global_session_priv_key_id} in
  let receiver_comm_keys_sess_ids = {pki=receiver_global_session_pub_key_id; private_keys=receiver_global_session_priv_key_id} in
  return (Some (client_comm_keys_sess_ids, receiver_comm_keys_sess_ids))

val encrypt_message: principal -> principal -> bytes -> bytes -> bytes -> bytes
let encrypt_message sender receiver payload pk nonce =
  let msg = {sender; receiver; payload} in
  let msg_bytes = serialize communication_message msg in
  pk_enc pk nonce msg_bytes

val send_confidential: 
  communication_keys_sess_ids ->
  principal -> principal -> bytes ->
  traceful (option timestamp)
let send_confidential keys_sess_ids sender receiver payload =
  let*? pk_receiver = get_public_key sender keys_sess_ids.pki (PkEnc "DY.Lib.Communication.PublicKey") receiver in
  let* nonce = mk_rand PkNonce (principal_label sender) 32 in
  let msg_encrypted = encrypt_message sender receiver payload pk_receiver nonce in
  let* msg_id = send_msg msg_encrypted in
  return (Some msg_id)


val decrypt_message: bytes -> bytes -> option communication_message
let decrypt_message sk_receiver msg_encrypted =
  let? msg_plain_bytes = pk_dec sk_receiver msg_encrypted in
  let? msg_plain = parse communication_message msg_plain_bytes in
  Some msg_plain

val receive_confidential:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option communication_message)
let receive_confidential keys_sess_ids receiver msg_id =
  let*? sk_receiver = get_private_key receiver keys_sess_ids.private_keys (PkDec "DY.Lib.Communication.PublicKey") in
  let*? msg_encrypted = recv_msg msg_id in
  return (decrypt_message sk_receiver msg_encrypted)

(*** Lemmas ***)

val contains_communication_layer_predicates:
  {|cinvs:crypto_invariants|} ->
  prop
let contains_communication_layer_predicates #cinvs =
  forall tr pk msg. (build_crypto_predicates (fun tr' pk' msg' -> False)).pkenc_pred tr pk msg ==>
    cinvs.preds.pkenc_pred tr pk msg

val contains_communication_layer_predicates2:
  {|cinvs:crypto_invariants|} ->
  prop
let contains_communication_layer_predicates2 #cinvs =
  forall tr pk msg. cinvs.preds.pkenc_pred tr pk msg ==>
    (build_crypto_predicates (fun tr' pk' msg' -> False)).pkenc_pred tr pk msg

val encrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal -> payload:bytes ->
  pk:bytes -> nonce:bytes ->
  Lemma
  (requires
    contains_communication_layer_predicates #cinvs /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
    is_secret (principal_label sender) tr nonce /\
    PkNonce? (get_usage nonce) /\
    is_encryption_key "DY.Lib.Communication.PublicKey" (principal_label receiver) tr pk
  )
  (ensures
    is_publishable tr (encrypt_message sender receiver payload pk nonce)
  )
let encrypt_message_proof #cinvs tr sender receiver payload pk nonce =
  let msg = {sender; receiver; payload} in

  assert(bytes_invariant tr payload);
  assert(bytes_invariant tr nonce);
  assert(bytes_invariant tr pk);

  let msg_encrypted = encrypt_message sender receiver payload pk nonce in
  
  serialize_wf_lemma communication_message (is_knowable_by (join (principal_label sender) (principal_label receiver)) tr) msg;
  serialize_wf_lemma communication_message (bytes_invariant tr) msg;
  assert(bytes_invariant tr (serialize communication_message msg));


  assert(get_sk_usage pk == PkdecKey "DY.Lib.Communication.PublicKey");
  assert(get_sk_label pk == principal_label receiver /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload);
  assert(cinvs.preds.pkenc_pred tr pk (serialize communication_message msg));
  assert(bytes_invariant tr msg_encrypted);
  ()

val send_confidential_proof:
  {|invs:protocol_invariants|} ->
  tr:trace -> 
  keys_sess_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\ has_pki_invariant invs /\ contains_communication_layer_predicates #invs.crypto_invs /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
  )
  (ensures (
    let (_, tr_out) = send_confidential keys_sess_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
let send_confidential_proof #invs tr keys_sess_ids sender receiver payload =
  match get_public_key sender keys_sess_ids.pki (PkEnc "DY.Lib.Communication.PublicKey") receiver tr with
  | (None, tr) -> ()
  | (Some pk_receiver, tr) -> (
    let (nonce, tr) = mk_rand PkNonce (principal_label sender) 32 tr in
    encrypt_message_proof tr sender receiver payload pk_receiver nonce;
    ()
  )

#push-options "--fuel 8 --ifuel 8 --z3rlimit 25"
val decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  receiver:principal -> sk_receiver:bytes -> msg_encrypted:bytes ->  
  Lemma
  (requires
    contains_communication_layer_predicates2 #cinvs /\
    is_decryption_key "DY.Lib.Communication.PublicKey" (principal_label receiver) tr sk_receiver /\
    bytes_invariant tr msg_encrypted
  )
  (ensures (
    match decrypt_message sk_receiver msg_encrypted with
    | None -> True
    | Some {sender; receiver=receiver'; payload} -> (
      let Some msg_plain = pk_dec sk_receiver msg_encrypted in
      (//PkdecKey? (get_sk_usage (Pk sk_receiver)) /\ 
        //cinvs.preds.pkenc_pred tr (Pk sk_receiver) msg_plain /\
        //get_sk_label (Pk sk_receiver) == principal_label receiver /\
        is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload) // \/
        //is_publishable tr payload
        //is_corrupt tr (principal_label receiver)
    )
  ))
let decrypt_message_proof #cinvs tr receiver sk_receiver msg_encrypted =
  match decrypt_message sk_receiver msg_encrypted with
  | None -> ()
  | Some {sender; receiver=receiver'; payload} -> ( 
    reveal_opaque (`%pk_dec) (pk_dec);
    normalize_term_spec (bytes_invariant);

    let Some msg_plain = pk_dec sk_receiver msg_encrypted in
    let (DY.Core.Bytes.Type.PkEnc pk nonce res) = msg_encrypted in
    assert(get_usage sk_receiver == PkdecKey "DY.Lib.Communication.PublicKey");
    
    assert((PkdecKey? (get_sk_usage pk) /\
      cinvs.preds.pkenc_pred tr pk msg_plain /\
      (get_label msg_plain) `can_flow tr` (get_sk_label pk) /\
      (get_label msg_plain) `can_flow tr` (get_label nonce) /\
      PkNonce? (get_usage nonce)
      ) \/ (
      (get_label pk) `can_flow tr` public /\
      (get_label nonce) `can_flow tr` public /\
      (get_label res) `can_flow tr` public
      )
    );

    // B -> A
    // A -> B
    assert(PkdecKey? (get_sk_usage pk) /\ 
      cinvs.preds.pkenc_pred tr pk msg_plain ==>
        (build_crypto_predicates (fun tr' pk' msg' -> False)).pkenc_pred tr pk msg_plain);

    // A -> C
    // A -> C
    assert(PkdecKey? (get_sk_usage pk) /\ 
      (build_crypto_predicates (fun tr' pk' msg' -> False)).pkenc_pred tr pk msg_plain ==>
      ((match parse communication_message msg_plain with
      | Some {sender; receiver; payload} -> (
        get_sk_label pk == principal_label receiver /\
        (get_label payload) `can_flow tr` (join (principal_label sender) (principal_label receiver))
      )
      | None -> False)));

    // B -> C
    // B -> C
    assert(PkdecKey? (get_sk_usage pk) /\ 
      cinvs.preds.pkenc_pred tr pk msg_plain ==>
      ((match parse communication_message msg_plain with
      | Some {sender; receiver; payload} -> (
        get_sk_label pk == principal_label receiver /\
        (get_label payload) `can_flow tr` (join (principal_label sender) (principal_label receiver))
      )
      | None -> False)));
    
    assert((get_sk_label pk == principal_label receiver' /\
      (get_label payload) `can_flow tr` (join (principal_label sender) (principal_label receiver'))) \/
      (
      (get_label pk) `can_flow tr` public /\
      (get_label nonce) `can_flow tr` public /\
      (get_label res) `can_flow tr` public
      ));

    FStar.Classical.move_requires (parse_wf_lemma communication_message (is_publishable tr)) msg_plain;
    FStar.Classical.move_requires (parse_wf_lemma communication_message (bytes_invariant tr)) msg_plain;
    assert(bytes_invariant tr payload);
    assert(is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload \/
      is_publishable tr payload);

    assert(is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload);
    ()
  )

val receive_confidential_proof:
  {|invs:protocol_invariants|} -> tr:trace -> comm_keys_ids:communication_keys_sess_ids ->
  receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\ 
    has_private_keys_invariant invs
  )
  (ensures (
    let (_, tr_out) = receive_confidential comm_keys_ids receiver msg_id tr in
    trace_invariant tr_out
  ))
let receive_confidential_proof #invs tr comm_keys_ids receiver msg_id = ()
