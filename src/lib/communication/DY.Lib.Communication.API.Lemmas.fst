module DY.Lib.Communication.API.Lemmas

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys

open DY.Lib.Communication.API
open DY.Lib.Communication.API.Predicates

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

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
    is_encryption_key (PkKey comm_layer_tag empty) (principal_label receiver) tr pk
  )
  (ensures
    is_publishable tr (encrypt_message sender receiver payload pk nonce)
  )
let encrypt_message_proof #cinvs tr sender receiver payload pk nonce =
  let msg = {sender; receiver; payload} in
  let msg_encrypted = encrypt_message sender receiver payload pk nonce in
  
  serialize_wf_lemma communication_message (is_knowable_by (join (principal_label sender) (principal_label receiver)) tr) msg;
  serialize_wf_lemma communication_message (bytes_invariant tr) msg;
  assert(bytes_invariant tr (serialize communication_message msg));
  
  assert(match get_sk_usage pk with
    | PkKey pkenc_tag _ ->
        pkenc_tag = comm_layer_tag ==>
          pkenc_pred.pred tr pk (serialize communication_message msg) == 
            (pkenc_crypto_predicates_communication_layer cinvs.usages).pred tr pk (serialize communication_message msg)
    | _ -> True);

  assert(cinvs.preds.pkenc_pred.pred tr pk (serialize communication_message msg));
  assert(bytes_invariant tr msg_encrypted);
  ()

val send_confidential_proof:
  {|invs:protocol_invariants|} ->
  tr:trace -> 
  keys_sess_ids:communication_keys_sess_ids ->
  sender:principal -> receiver:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\ has_pki_invariant invs /\ has_communication_layer_invariants invs.crypto_invs /\
    is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload
  )
  (ensures (
    let (_, tr_out) = send_confidential keys_sess_ids sender receiver payload tr in
    trace_invariant tr_out
  ))
let send_confidential_proof #invs tr keys_sess_ids sender receiver payload =
  match get_public_key sender keys_sess_ids.pki (PkEnc comm_layer_tag) receiver tr with
  | (None, tr) -> ()
  | (Some pk_receiver, tr) -> (
    let (nonce, tr) = mk_rand PkNonce (principal_label sender) 32 tr in
    encrypt_message_proof tr sender receiver payload pk_receiver nonce;
    ()
  )


val decrypt_message_proof:
  {|cinvs:crypto_invariants|} ->
  tr:trace ->
  receiver:principal -> sk_receiver:bytes -> msg_encrypted:bytes ->  
  Lemma
  (requires
    has_communication_layer_invariants cinvs /\
    is_decryption_key (PkKey comm_layer_tag empty) (principal_label receiver) tr sk_receiver /\
    bytes_invariant tr msg_encrypted
  )
  (ensures (
    match decrypt_message sk_receiver msg_encrypted with
    | None -> True
    | Some {sender; receiver=receiver'; payload} -> (
      let Some msg_plain = pk_dec sk_receiver msg_encrypted in
      (//
        // /\
        //get_sk_label (Pk sk_receiver) == principal_label receiver /\
        is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload ///\
        //(pkenc_pred.pred tr (Pk sk_receiver) msg_plain \/
        //is_publishable tr msg_plain)
        //is_corrupt tr (principal_label receiver)
      )
    )
  ))
let decrypt_message_proof #cinvs tr receiver sk_receiver msg_encrypted =
  match decrypt_message sk_receiver msg_encrypted with
  | None -> ()
  | Some {sender; receiver=receiver'; payload} -> ( 
    let Some msg_plain = pk_dec sk_receiver msg_encrypted in
    let pk = pk sk_receiver in
    
    assert(get_usage sk_receiver == PkKey comm_layer_tag empty);
 
    // This follows from the precondition:
    // has_communication_layer_invariants invs.crypto_invs
    assert(match get_sk_usage pk with
          | PkKey pkenc_tag _ ->
            pkenc_tag = comm_layer_tag ==>
              pkenc_pred.pred tr pk msg_plain == 
                (pkenc_crypto_predicates_communication_layer cinvs.usages).pred tr pk msg_plain
          | _ -> True
    );
    // Since the precondition states that pk has the
    // comm_layer_tag, we can directly assert that the
    // predicates are equal.
    assert(pkenc_pred.pred tr pk msg_plain == 
                (pkenc_crypto_predicates_communication_layer cinvs.usages).pred tr pk msg_plain);

    // From the crypto predicates we can infer that the
    // payload can flow to the sender and the receiver
    assert((pkenc_crypto_predicates_communication_layer cinvs.usages).pred tr pk msg_plain ==>
          (match parse communication_message msg_plain with
            | Some {sender; receiver; payload} -> (
              get_sk_label pk == principal_label receiver /\
              (get_label payload) `can_flow tr` (join (principal_label sender) (principal_label receiver))
            )
            | None -> False)
    );

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