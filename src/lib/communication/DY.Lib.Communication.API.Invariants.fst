module DY.Lib.Communication.API.Invariants

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed

open DY.Lib.Communication.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** PkEnc Predicates ***)

val pkenc_crypto_predicates_communication_layer: cusages:crypto_usages -> pkenc_crypto_predicate cusages
let pkenc_crypto_predicates_communication_layer cusages = {
  pred = (fun tr pk msg ->
    get_sk_usage pk == PkKey comm_layer_pkenc_tag empty /\
    (exists sender receiver.
      get_sk_label pk == principal_label receiver /\
      (get_label msg) `can_flow tr` (join (principal_label sender) (principal_label receiver)) /\
      event_triggered tr sender (CommConfSendMsg sender receiver msg)
    ));
  pred_later = (fun tr1 tr2 pk msg -> ());
}

val pkenc_crypto_predicates_communication_layer_and_tag: 
  {|cusages:crypto_usages|} ->
  (string & pkenc_crypto_predicate cusages)
let pkenc_crypto_predicates_communication_layer_and_tag #cusages = 
  (comm_layer_pkenc_tag, pkenc_crypto_predicates_communication_layer cusages)

(*** Sign Predicates ***)

(*val pk_enc_extract_msg: enc_msg:bytes -> option bytes
let pk_enc_extract_msg enc_msg =
  match enc_msg with
  | DY.Core.Bytes.Type.PkEnc pk nonce msg -> Some msg
  | _ -> None

val pk_enc_extract_sk: enc_msg:bytes -> option bytes
let pk_enc_extract_sk enc_msg =
  match enc_msg with
  | DY.Core.Bytes.Type.PkEnc pk nonce msg -> (
    match pk with
    | DY.Core.Bytes.Type.Pk sk -> Some sk
    | _ -> None
  )
  | _ -> None*)

#push-options "--ifuel 3 --fuel 0"
val sign_crypto_predicates_communication_layer: cusages:crypto_usages -> sign_crypto_predicate cusages
let sign_crypto_predicates_communication_layer cusages = {
  pred = (fun tr vk sig_msg ->
    get_signkey_usage vk == SigKey comm_layer_sign_tag empty /\
    (match parse signature_input sig_msg with
    | Some (Plain {sender; receiver; payload}) -> (
      get_signkey_label vk == principal_label sender /\
      get_label payload `can_flow tr` public /\
      event_triggered tr sender (CommAuthSendMsg sender payload)
    )
    | Some (Encrypted {sender; receiver; payload=enc_payload}) -> (      
      get_signkey_label vk == principal_label sender /\
      get_label enc_payload `can_flow tr` public /\
      
      (exists plain_msg nonce pk_receiver.
        //pk_enc_extract_pk enc_payload == Some (DY.Core.Bytes.Type.Pk sk_receiver) /\
        //Some plain_msg == decrypt_message sk_receiver enc_payload /\
        //get_label sk_receiver == principal_label receiver /\
        enc_payload == encrypt_message pk_receiver nonce plain_msg /\
        //event_triggered tr sender (CommConfSendMsg sender receiver plain_msg) /\
        //event_triggered tr sender (CommAuthSendMsg sender plain_msg) /\
        event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_msg) //\
        //get_label plain_msg `can_flow tr` (join (principal_label sender) (principal_label receiver))
      )
      (*match payload with
      | DY.Core.Bytes.Type.PkEnc pk nonce msg -> (
        get_sk_usage pk == PkKey comm_layer_pkenc_tag empty /\
        get_sk_label pk == principal_label receiver /\
        get_label msg `can_flow tr` (join (principal_label sender) (principal_label receiver)) /\
        event_triggered tr sender (CommConfSendMsg sender receiver msg)
      )
      | _ -> False*)
    )
    | None -> False)
  );
  pred_later = (fun tr1 tr2 vk msg -> ());
}
#pop-options

val sign_crypto_predicates_communication_layer_and_tag: 
  {|cusages:crypto_usages|} ->
  (string & sign_crypto_predicate cusages)
let sign_crypto_predicates_communication_layer_and_tag #cusages =
  (comm_layer_sign_tag, sign_crypto_predicates_communication_layer cusages)

val has_communication_layer_invariants:
  crypto_invariants ->
  prop
let has_communication_layer_invariants cinvs =
  has_pkenc_predicate cinvs pkenc_crypto_predicates_communication_layer_and_tag /\
  has_sign_predicate cinvs sign_crypto_predicates_communication_layer_and_tag

(*** Event Predicates ***)

noeq
type comm_higher_layer_event_preds = {
  send_conf: sender:principal -> receiver:principal -> payload:bytes -> tr:trace -> prop;
  send_auth: sender:principal -> payload:bytes -> tr:trace -> prop;
  send_conf_auth: sender:principal -> receiver:principal -> payload:bytes -> tr:trace -> prop;
}

val default_comm_higher_layer_event_preds: comm_higher_layer_event_preds
let default_comm_higher_layer_event_preds = {
  send_conf = (fun sender receiver payload tr -> True);
  send_auth = (fun sender payload tr -> True);
  send_conf_auth = (fun sender receiver payload tr -> True);
}

val comm_layer_preds_later: trace -> (trace -> prop) -> prop
let comm_layer_preds_later tr higher_layer_preds =
  forall tr'. tr <$ tr' ==> higher_layer_preds tr'

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer {|cinvs:crypto_invariants|} (higher_layer_preds:comm_higher_layer_event_preds) : event_predicate communication_event =
  fun tr prin e ->
    (match e with
    | CommConfSendMsg sender receiver payload -> (
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
      higher_layer_preds.send_conf sender receiver payload tr
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
      higher_layer_preds.send_auth sender payload tr
    )
    | CommAuthReceiveMsg sender receiver payload -> (
      is_publishable tr payload /\
      (
        (
          event_triggered tr sender (CommAuthSendMsg sender payload)
        ) \/
        is_corrupt tr (principal_label sender)
      )
    )
    | CommConfAuthSendMsg sender receiver payload -> (
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
      higher_layer_preds.send_conf_auth sender receiver payload tr
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
      is_corrupt tr (principal_label sender)
    ))
#pop-options

val event_predicate_communication_layer_and_tag: 
  {|cinvs:crypto_invariants|} ->
  comm_higher_layer_event_preds ->
  (string & compiled_event_predicate)
let event_predicate_communication_layer_and_tag #cinvs higher_layer_preds =
  ("DY.Lib.Communication.Event", compile_event_pred #communication_event (event_predicate_communication_layer #cinvs higher_layer_preds))

val has_communication_layer_event_predicates:
  protocol_invariants ->
  comm_higher_layer_event_preds ->
  prop
let has_communication_layer_event_predicates invs higher_layer_preds =
  has_event_pred invs (event_predicate_communication_layer higher_layer_preds)
