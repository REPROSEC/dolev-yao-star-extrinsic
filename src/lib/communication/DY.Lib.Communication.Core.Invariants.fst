module DY.Lib.Communication.Core.Invariants

open Comparse
open DY.Core
open DY.Lib.Communication.Core.Extension
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Crypto.AEAD.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Tagged

open DY.Lib.Communication.Core

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** PkEnc Predicates ***)

#push-options "--ifuel 3 --fuel 0"
val pkenc_crypto_predicates_communication_layer: {|cusages:crypto_usages|} -> pkenc_crypto_predicate
let pkenc_crypto_predicates_communication_layer #cusages = {
  pred = (fun tr sk_usage msg ->
    match parse pkenc_input msg with
    | Some (PkEncInput payload) -> (
      (exists sender receiver.
        sk_usage == long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag)  receiver /\
        (get_label tr payload) `can_flow tr` (join (principal_label sender) (principal_label receiver)) /\
        event_triggered tr sender (CommConfSendMsg sender receiver payload)
      )
    )
    | Some (PkEncSignInput {sender; receiver; payload}) -> (
      sk_usage == long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag)  receiver /\
      (get_label tr payload) `can_flow tr` (join (principal_label sender) (principal_label receiver)) /\
      event_triggered tr sender (CommConfSendMsg sender receiver payload) /\
      event_triggered tr sender (CommConfAuthSendMsg sender receiver payload)
    )
    | None -> False
    );
  pred_later = (fun tr1 tr2 pk msg -> parse_wf_lemma pkenc_input (bytes_well_formed tr1) msg);
}
#pop-options

val pkenc_crypto_predicates_communication_layer_and_tag: 
  {|cusages:crypto_usages|} ->
  (string & pkenc_crypto_predicate)
let pkenc_crypto_predicates_communication_layer_and_tag #cusages = 
  (comm_layer_pkenc_tag, pkenc_crypto_predicates_communication_layer)

(*** Sign Predicates ***)

(*
val pk_enc_extract_msg: enc_msg:bytes{exists pk nonce msg. enc_msg = pk_enc pk nonce msg} -> GTot (msg:bytes{exists pk nonce. enc_msg = pk_enc pk nonce msg})
let pk_enc_extract_msg enc_msg =
  normalize_term_spec pk_enc;
  match enc_msg with
  | DY.Core.Bytes.Type.PkEnc pk nonce msg -> msg

val pk_enc_extract_sk: enc_msg:bytes -> option bytes
let pk_enc_extract_sk enc_msg =
  match enc_msg with
  | DY.Core.Bytes.Type.PkEnc pk nonce msg -> (
    match pk with
    | DY.Core.Bytes.Type.Pk sk -> Some sk
    | _ -> None
  )
  | _ -> None*)

#push-options "--ifuel 4 --fuel 4 --z3rlimit 50"
val sign_crypto_predicates_communication_layer: {|cusages:crypto_usages|} -> sign_crypto_predicate
let sign_crypto_predicates_communication_layer #cusages = {
  pred = (fun tr sk_usage vk sig_msg ->
    (match parse signature_input sig_msg with
    | Some (Plain {sender; receiver; payload}) -> (
      sk_usage == long_term_key_type_to_usage (LongTermSigKey comm_layer_sign_tag) sender /\
      get_label tr payload `can_flow tr` public /\
      event_triggered tr sender (CommAuthSendMsg sender payload)
    )
    | Some (Encrypted payload) -> (  
      get_label tr payload `can_flow tr` public /\

      (exists (plain_payload:communication_message) nonce pk_receiver.
        sk_usage == long_term_key_type_to_usage (LongTermSigKey comm_layer_sign_tag) plain_payload.sender /\

        //pk_enc_extract_pk enc_payload == Some (DY.Core.Bytes.Type.Pk sk_receiver) /\
        //Some plain_msg == decrypt_message sk_receiver enc_payload /\
        //get_label sk_receiver == principal_label receiver /\
        bytes_well_formed tr pk_receiver /\
        pk_receiver `has_sk_usage tr` (long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag) plain_payload.receiver) /\
        payload == encrypt_message pk_receiver nonce (PkEncSignInput plain_payload) /\
        //event_triggered tr sender (CommConfSendMsg sender receiver plain_msg) /\
        //event_triggered tr sender (CommAuthSendMsg sender plain_msg) /\
        event_triggered tr plain_payload.sender (CommConfAuthSendMsg plain_payload.sender plain_payload.receiver plain_payload.payload) //\
        //get_label plain_msg `can_flow tr` (join (principal_label sender) (principal_label receiver))
      )
    )
    | None -> False)
  );
  pred_later = (fun tr1 tr2 sk_usage msg -> parse_wf_lemma signature_input (bytes_well_formed tr1) msg);
}
#pop-options

val sign_crypto_predicates_communication_layer_and_tag: 
  {|cusages:crypto_usages|} ->
  (string & sign_crypto_predicate)
let sign_crypto_predicates_communication_layer_and_tag #cusages =
  (comm_layer_sign_tag, sign_crypto_predicates_communication_layer)

val has_communication_layer_crypto_predicates:
  {|crypto_invariants|} ->
  prop
let has_communication_layer_crypto_predicates #cinvs =
  has_pkenc_predicate pkenc_crypto_predicates_communication_layer_and_tag /\
  has_sign_predicate sign_crypto_predicates_communication_layer_and_tag

(*** Event Predicates ***)

noeq
type comm_higher_layer_event_preds = {
  send_conf: tr:trace -> sender:principal -> receiver:principal -> payload:bytes -> prop;
  send_conf_later: 
    tr1:trace -> tr2:trace ->
    sender:principal -> receiver:principal -> payload:bytes ->
    Lemma
    (requires
      send_conf tr1 sender receiver payload /\
      bytes_well_formed tr1 payload /\
      tr1 <$ tr2
    )
    (ensures send_conf tr2 sender receiver payload)
  ;
  send_auth: tr:trace -> sender:principal -> payload:bytes -> prop;
  send_auth_later: 
    tr1:trace -> tr2:trace ->
    sender:principal -> payload:bytes ->
    Lemma
    (requires
      send_auth tr1 sender payload /\
      bytes_well_formed tr1 payload /\
      tr1 <$ tr2
    )
    (ensures send_auth tr2 sender payload)
  ;
  send_conf_auth: tr:trace -> sender:principal -> receiver:principal -> payload:bytes -> prop;
  send_conf_auth_later: 
    tr1:trace -> tr2:trace ->
    sender:principal -> receiver:principal -> payload:bytes ->
    Lemma
    (requires
      send_conf_auth tr1 sender receiver payload /\
      bytes_well_formed tr1 payload /\
      tr1 <$ tr2
    )
    (ensures send_conf_auth tr2 sender receiver payload)
}

val default_comm_higher_layer_event_preds: comm_higher_layer_event_preds
let default_comm_higher_layer_event_preds = {
  send_conf = (fun tr sender receiver payload -> True);
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ());
  send_auth = (fun tr sender payload -> True);
  send_auth_later = (fun tr1 tr2 sender payload -> ());
  send_conf_auth = (fun tr sender receiver payload -> True);
  send_conf_auth_later = (fun tr1 tr2 sender receiver payload -> ())
}

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer 
  {|cinvs:crypto_invariants|}
  (higher_layer_preds:comm_higher_layer_event_preds) : 
  event_predicate communication_event =
  fun tr prin e ->
    (match e with
    | CommConfSendMsg sender receiver payload -> (
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
      higher_layer_preds.send_conf tr sender receiver payload
    )
    | CommConfReceiveMsg receiver payload -> (
      exists sender.
        is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
        (
          event_triggered tr sender (CommConfSendMsg sender receiver payload) \/
          is_publishable tr payload
        )
    )
    | CommAuthSendMsg sender payload -> (
      higher_layer_preds.send_auth tr sender payload
    )
    | CommAuthReceiveMsg sender receiver payload -> (
      is_publishable tr payload /\
      (
        event_triggered tr sender (CommAuthSendMsg sender payload) \/
        is_corrupt tr (long_term_key_label sender)
      )
    )
    | CommConfAuthSendMsg sender receiver payload -> (
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
      higher_layer_preds.send_conf_auth tr sender receiver payload
    )
    | CommConfAuthReceiveMsg sender receiver payload -> (
      // We can only show the following about the decrypted ciphertext (payload):
      // is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload \/
      // is_corrupt tr (principal_label sender)
      // There are two cases how the ciphertext is created:
      // 1. The corrupted sender created the ciphertext. This means that the
      //    payload flows to public. This would also mean that it flows to the
      //    sender and receiver. The problem is the second case.
      // 2. The corrupted sender takes a ciphertext from an honest principal.
      //    Since the crypto predicates apply to this ciphertext, the
      //    decrypted payload flows to the receiver and some unknown sender'.
      event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) \/
      is_corrupt tr (long_term_key_label sender)
    )
    )
#pop-options

val event_predicate_communication_layer_and_tag: 
  {|cinvs:crypto_invariants|} ->
  comm_higher_layer_event_preds ->
  (string & compiled_event_predicate)
let event_predicate_communication_layer_and_tag #cinvs higher_layer_preds =
  (event_communication_event.tag, compile_event_pred (event_predicate_communication_layer #cinvs higher_layer_preds))

val has_communication_layer_event_predicates:
  {|protocol_invariants|} ->
  comm_higher_layer_event_preds ->
  prop
let has_communication_layer_event_predicates #invs higher_layer_preds =
  has_event_pred (event_predicate_communication_layer #invs.crypto_invs higher_layer_preds)
