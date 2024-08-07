module DY.Lib.Communication.API.Predicates

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed

open DY.Lib.Communication.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** PkEnc Predicates ***)

#push-options "--ifuel 3 --fuel 0"
val pkenc_crypto_predicates_communication_layer: cusages:crypto_usages -> pkenc_crypto_predicate cusages
let pkenc_crypto_predicates_communication_layer cusages = {
  pred = (fun tr pk msg ->
    get_sk_usage pk == PkKey comm_layer_pkenc_tag empty /\
      (match parse communication_message msg with
      | Some (CM {sender; receiver; payload}) -> (
        get_sk_label pk == principal_label receiver /\
        (get_label payload) `can_flow tr` (join (principal_label sender) (principal_label receiver)) /\
        event_triggered tr sender (CommConfSendMsg sender receiver payload)
      )
      | _ -> False)
    );
  pred_later = (fun tr1 tr2 pk msg -> ());
}
#pop-options

val pkenc_crypto_predicates_communication_layer_and_tag: 
  {|cusages:crypto_usages|} ->
  (string & pkenc_crypto_predicate cusages)
let pkenc_crypto_predicates_communication_layer_and_tag #cusages = 
  (comm_layer_pkenc_tag, pkenc_crypto_predicates_communication_layer cusages)

(*** Sign Predicates ***)

#push-options "--ifuel 3 --fuel 0"
val sign_crypto_predicates_communication_layer: cusages:crypto_usages -> sign_crypto_predicate cusages
let sign_crypto_predicates_communication_layer cusages = {
  pred = (fun tr vk sig_msg ->
    get_signkey_usage vk == SigKey comm_layer_sign_tag empty /\
    (match parse communication_message sig_msg with
    | Some (CM {sender; receiver; payload}) -> (
      get_signkey_label vk == principal_label sender /\
      get_label payload `can_flow tr` public /\
      event_triggered tr sender (CommAuthSendMsg sender payload)
    )
    | _ -> False)
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
  send_conf: tr:trace -> sender:principal -> receiver:principal -> payload:bytes -> prop;
  receive_conf: tr:trace -> sender:principal -> receiver:principal -> payload:bytes -> prop;
  send_auth: tr:trace -> sender:principal -> payload:bytes -> prop;
  receive_auth: tr:trace -> sender:principal -> receiver:principal -> vk_sender:bytes -> payload:bytes -> prop;
}

val default_comm_higher_layer_event_preds: comm_higher_layer_event_preds
let default_comm_higher_layer_event_preds = {
  send_conf = (fun tr sender receiver payload -> True);
  receive_conf = (fun tr sender receiver payload -> True);
  send_auth = (fun tr sender payload -> True);
  receive_auth = (fun tr sender receiver vk_sender payload -> True);
}

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer {|cinvs:crypto_invariants|} (higher_layer_preds:comm_higher_layer_event_preds) : event_predicate communication_event =
  fun tr prin e ->
    (match e with
    | CommConfSendMsg sender receiver payload -> (
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
      higher_layer_preds.send_conf tr sender receiver payload
    )
    | CommConfReceiveMsg sender receiver payload -> (
      (
        event_triggered tr sender (CommConfSendMsg sender receiver payload) /\
        is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
        higher_layer_preds.receive_conf tr sender receiver payload
      ) \/ (
        is_publishable tr payload
      )
    )
    | CommAuthSendMsg sender payload -> (
      higher_layer_preds.send_auth tr sender payload
    )
    | CommAuthReceiveMsg sender receiver vk_sender payload -> (
      is_publishable tr payload /\
      (
        (
          event_triggered tr sender (CommAuthSendMsg sender payload) /\
          higher_layer_preds.receive_auth tr sender receiver vk_sender payload
        ) \/
        is_corrupt tr (get_signkey_label vk_sender)
      )
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
