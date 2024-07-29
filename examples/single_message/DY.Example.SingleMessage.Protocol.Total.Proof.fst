module DY.Example.SingleMessage.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleMessage.Protocol.Total
open DY.Example.SingleMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

val crypto_usages_protocol: crypto_usages
instance crypto_usages_protocol = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
val pkenc_predicate_protocol: cusages:crypto_usages -> pkenc_crypto_predicate cusages
let pkenc_predicate_protocol cusages = {
  pred = (fun tr pk msg ->
    get_sk_usage pk == PkKey "DY.Example.SingleMessage.PublicKey" empty /\
      (match parse message msg with
      | Some (Test test_msg) -> (
        (exists receiver. get_sk_label pk == principal_label receiver /\
        get_label test_msg.secret == join (principal_label test_msg.sender) (principal_label receiver) /\
        event_triggered tr test_msg.sender (ClientSendMsg test_msg.sender receiver test_msg.secret))
      )
      | _ -> False)
  );
  pred_later = (fun tr1 tr2 pk msg -> ());
}
#pop-options

val pkenc_pred_list_protocol: list (string & pkenc_crypto_predicate crypto_usages_protocol)
let pkenc_pred_list_protocol = [
  pkenc_crypto_predicates_communication_layer_and_tag;
  ("DY.Example.SingleMessage.PublicKey", pkenc_predicate_protocol crypto_usages_protocol)
]

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_protocol: crypto_predicates crypto_usages_protocol
let crypto_predicates_protocol = {
  default_crypto_predicates crypto_usages_protocol with

  pkenc_pred = mk_pkenc_predicate pkenc_pred_list_protocol;
}

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}
#pop-options

val crypto_invariants_protocol_has_all_predicates: 
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%pkenc_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP (has_pkenc_predicate crypto_invariants_protocol) pkenc_pred_list_protocol
    )
  )
let crypto_invariants_protocol_has_all_predicates () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (pkenc_pred_list_protocol)));
  mk_pkenc_predicate_correct crypto_invariants_protocol pkenc_pred_list_protocol;
  norm_spec [delta_only [`%pkenc_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP (has_pkenc_predicate crypto_invariants_protocol) pkenc_pred_list_protocol);
  ()

// TODO ask why this is needed so that in the stateful proof line 126 
// (assert(has_communication_layer_invariants crypto_invariants_protocol);)
// works.
val protocol_crypto_invariants_has_communication_layer_invariants: squash (has_communication_layer_invariants crypto_invariants_protocol)
let protocol_crypto_invariants_has_communication_layer_invariants =
  crypto_invariants_protocol_has_all_predicates ()

val has_local_invariants:
  crypto_invariants ->
  prop
let has_local_invariants cinvs =
  has_pkenc_predicate cinvs (
    "DY.Example.SingleMessage.PublicKey",
    pkenc_predicate_protocol cinvs.usages
  )

val protocol_crypto_invariants_has_local_invariants: squash (has_local_invariants crypto_invariants_protocol)
let protocol_crypto_invariants_has_local_invariants =
  crypto_invariants_protocol_has_all_predicates ()

(*** Proofs ***)

val compute_message_proof:
  tr:trace ->
  client:principal -> server:principal ->
  secret:bytes ->
  Lemma
  (requires
    event_triggered tr client (ClientSendMsg client server secret) /\
    bytes_invariant tr secret /\
    is_knowable_by (join (principal_label client) (principal_label server)) tr secret
  )
  (ensures
    is_knowable_by (join (principal_label client) (principal_label server)) tr (compute_message secret)
  )
let compute_message_proof tr client server secret =
  serialize_wf_lemma message (is_knowable_by (join (principal_label client) (principal_label server)) tr) (Msg {secret;});
  ()

val decode_message_proof:
  tr:trace ->
  client:principal -> server:principal ->
  msg_bytes:bytes ->
  Lemma
  (requires
    is_knowable_by (join (principal_label client) (principal_label server)) tr msg_bytes \/
    is_publishable tr msg_bytes
  )
  (ensures (
    match decode_message msg_bytes with
    | Some msg -> (
      is_knowable_by (join (principal_label client) (principal_label server)) tr msg.secret
    )
    | None -> True
  )
  )
let decode_message_proof tr client server msg_bytes =
  match decode_message msg_bytes with
  | Some msg -> (
    parse_wf_lemma message (is_knowable_by (join (principal_label client) (principal_label server)) tr) msg_bytes;
    ()
  )
  | None -> ()

val enc_test_local_predicates_proof:
  tr:trace ->
  sender:principal -> receiver:principal -> 
  pk:bytes -> nonce:bytes -> secret:bytes ->
  Lemma
  (requires
    is_secret (join (principal_label sender) (principal_label receiver)) tr secret /\
    is_secret (principal_label sender) tr nonce /\
    PkNonce? (get_usage nonce) /\
    is_encryption_key (PkKey "DY.Example.SingleMessage.PublicKey" empty) (principal_label receiver) tr pk /\
    event_triggered tr sender (ClientSendMsg sender receiver secret)
  )
  (ensures
    is_publishable tr (pk_enc pk nonce (serialize message (Test {sender; secret})))
  )
let enc_test_local_predicates_proof tr sender receiver pk nonce secret =
  assert(bytes_invariant tr secret);
  assert(bytes_invariant tr nonce);
  assert(bytes_invariant tr pk);
  serialize_wf_lemma message (is_knowable_by (join (principal_label sender) (principal_label receiver)) tr) (Test {sender; secret;});
  let plain = serialize message (Test {sender; secret}) in
  assert(bytes_invariant tr plain);
  assert(is_knowable_by (join (principal_label sender) (principal_label receiver)) tr plain);
  
  let enc = pk_enc pk nonce plain in

  reveal_opaque (`%pk_enc) (pk_enc);  
  let (DY.Core.Bytes.Type.PkEnc pk' nonce' plain') = enc in

  assert(get_sk_usage pk == PkKey "DY.Example.SingleMessage.PublicKey" empty /\
      (match parse message plain with
      | Some (Test test_msg) -> (
        (exists receiver. get_sk_label pk == principal_label receiver)
      )
      | None -> False));

  assert(match get_sk_usage pk with
    | PkKey pkenc_tag _ ->
        pkenc_tag = "DY.Example.SingleMessage.PublicKey" ==>
          pkenc_pred.pred tr pk plain == 
            (pkenc_predicate_protocol crypto_invariants_protocol.usages).pred tr pk plain
    | _ -> True);
  
  assert((pkenc_predicate_protocol crypto_invariants_protocol.usages).pred tr pk plain);
  assert(crypto_invariants_protocol.preds.pkenc_pred.pred tr pk plain);
  assert(bytes_invariant tr enc);
  assert(is_publishable tr enc);
  ()

val dec_test_local_predicates_proof:
  tr:trace ->
  receiver:principal -> 
  sk:bytes -> enc:bytes ->
  Lemma
  (requires
    is_publishable tr enc /\
    is_decryption_key (PkKey "DY.Example.SingleMessage.PublicKey" empty) (principal_label receiver) tr sk
  )
  (ensures
    (
      match pk_dec sk enc with
      | Some plain -> (
        match parse message plain with
        | Some (Test test_msg) -> (
          is_knowable_by (join (principal_label test_msg.sender) (principal_label receiver)) tr test_msg.secret /\
          (event_triggered tr test_msg.sender (ClientSendMsg test_msg.sender receiver test_msg.secret) \/
          is_publishable tr test_msg.secret)
        )
        | _ -> True
      )
      | None -> True
    
    )
  )
let dec_test_local_predicates_proof tr receiver sk enc =
  match pk_dec sk enc with
  | Some plain -> (
    assert(bytes_invariant tr plain);
    match parse message plain with
    | Some (Test test_msg) -> (
      
      FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) plain;
      FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) plain;
      FStar.Classical.move_requires (parse_wf_lemma message (is_knowable_by (join (principal_label test_msg.sender) (principal_label receiver)) tr)) plain;
      assert(exists s r. is_knowable_by (join (principal_label s) (principal_label r)) tr test_msg.secret);

      reveal_opaque (`%pk_dec) (pk_dec);  
      let (DY.Core.Bytes.Type.PkEnc pk nonce plain') = enc in

      assert(plain == plain');

      assert(pk == Pk sk);
      assert(is_decryption_key (PkKey "DY.Example.SingleMessage.PublicKey" empty) (principal_label receiver) tr sk);
      
      reveal_opaque (`%get_sk_usage) (get_sk_usage);       
      assert(get_sk_usage pk == (PkKey "DY.Example.SingleMessage.PublicKey" empty));
      assert(bytes_invariant tr sk);
      normalize_term_spec bytes_invariant;      
      assert(bytes_invariant tr pk);

      normalize_term_spec get_label;
      assert(is_publishable tr pk);
      reveal_opaque (`%get_sk_label) (get_sk_label);
      assert(exists r. is_encryption_key (PkKey "DY.Example.SingleMessage.PublicKey" empty) (principal_label r) tr pk);

      assert(match get_sk_usage pk with
        | PkKey pkenc_tag _ ->
            pkenc_tag = "DY.Example.SingleMessage.PublicKey" ==>
              pkenc_pred.pred tr pk plain == 
                (pkenc_predicate_protocol crypto_invariants_protocol.usages).pred tr pk plain
        | _ -> True);
     
      normalize_term_spec bytes_invariant;
      assert(pkenc_pred.pred tr pk plain \/ (
        // Attacker case:
        // the attacker knows the nonce, key and message
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label plain) `can_flow tr` public
      ));

      assert(match get_sk_usage pk with
        | PkKey pkenc_tag _ ->
            pkenc_tag = "DY.Example.SingleMessage.PublicKey" ==>
              (pkenc_predicate_protocol crypto_invariants_protocol.usages).pred tr pk plain \/ (
        // Attacker case:
        // the attacker knows the nonce, key and message
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label plain) `can_flow tr` public
      )
        | _ -> True);

      assert((pkenc_predicate_protocol crypto_invariants_protocol.usages).pred tr pk plain \/ (
        // Attacker case:
        // the attacker knows the nonce, key and message
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label plain) `can_flow tr` public
      ));

      assert((match parse message plain with
      | Some (Test test_msg) -> (
        (exists receiver. get_sk_label pk == principal_label receiver /\
        get_label test_msg.secret == join (principal_label test_msg.sender) (principal_label receiver) /\
        event_triggered tr test_msg.sender (ClientSendMsg test_msg.sender receiver test_msg.secret))
      )
      | _ -> False) \/ (
        // Attacker case:
        // the attacker knows the nonce, key and message
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label plain) `can_flow tr` public
      ));
 
      let Some (Test test_msg') = parse message plain in

      assert((exists s r. event_triggered tr s (ClientSendMsg s r test_msg.secret))  \/ (
        // Attacker case:
        // the attacker knows the nonce, key and message
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label plain) `can_flow tr` public
      ));

      assert(event_triggered tr test_msg.sender (ClientSendMsg test_msg.sender receiver test_msg.secret)  \/ (
        // Attacker case:
        // the attacker knows the nonce, key and message
        (get_label pk) `can_flow tr` public /\
        (get_label nonce) `can_flow tr` public /\
        (get_label plain) `can_flow tr` public
      ));
      ()
    )
    | _ -> ()
  )
  | None -> ()
