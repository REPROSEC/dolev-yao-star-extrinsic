module DY.Lib.Communication.Core.Invariants

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Crypto.AEAD.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Tagged
open DY.Lib.Comparse.DYUtils

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** PkEnc Predicates ***)

val pke_crypto_predicates_communication_layer: {|cusages:crypto_usages|} -> pke_crypto_predicate
let pke_crypto_predicates_communication_layer #cusages = {
  pred = (fun tr sk_usage pk msg ->
    (exists sender receiver.
      sk_usage == long_term_key_type_to_usage (LongTermPkeKey comm_layer_pkenc_tag)  receiver /\
      (get_label tr msg) `can_flow tr` (comm_label sender receiver) /\
      event_triggered tr sender (CommConfSendMsg sender receiver msg)
    )
    );
  pred_later = (fun tr1 tr2 sk_usage pk msg -> ());
}

val pke_crypto_predicates_communication_layer_and_tag:
  {|cusages:crypto_usages|} ->
  (string & pke_crypto_predicate)
let pke_crypto_predicates_communication_layer_and_tag #cusages =
  (comm_layer_pkenc_tag, pke_crypto_predicates_communication_layer)

(*** Sign Predicates ***)

#push-options "--ifuel 3 --fuel 0"
val sign_crypto_predicates_communication_layer: {|cusages:crypto_usages|} -> sign_crypto_predicate
let sign_crypto_predicates_communication_layer #cusages = {
  pred = (fun tr sk_usage vk sig_msg ->
    (match parse signature_input sig_msg with
    | Some (Plain sender receiver payload_bytes) -> (
      sk_usage == long_term_key_type_to_usage (LongTermSigKey comm_layer_sign_tag) sender /\
      get_label tr payload_bytes `can_flow tr` public /\
      event_triggered tr sender (CommAuthSendMsg sender payload_bytes)
    )
    | Some (Encrypted sender receiver payload_bytes pk_receiver) -> (
      match parse com_send_byte payload_bytes with
      | None -> False
      | Some payload -> (
        get_label tr payload_bytes `can_flow tr` public /\
        (exists plain_payload nonce.
          sk_usage == long_term_key_type_to_usage (LongTermSigKey comm_layer_sign_tag) sender /\
          payload.b == pke_enc pk_receiver nonce plain_payload /\
          event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
        )
      )
    )
    | None -> False)
  );
  pred_later = (fun tr1 tr2 sk_usage vk msg -> parse_wf_lemma signature_input (bytes_well_formed tr1) msg);
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
  has_pke_predicate pke_crypto_predicates_communication_layer_and_tag /\
  has_sign_predicate sign_crypto_predicates_communication_layer_and_tag

(*** Event Predicates ***)

noeq
type comm_higher_layer_event_preds (a:Type) {| parseable_serializeable bytes a |} = {
  send_conf: tr:trace -> sender:principal -> receiver:principal -> payload:a -> prop;
  send_conf_later:
    tr1:trace -> tr2:trace ->
    sender:principal -> receiver:principal -> payload:a ->
    Lemma
    (requires
      send_conf tr1 sender receiver payload /\
      is_well_formed a (bytes_well_formed tr1) payload /\
      tr1 <$ tr2
    )
    (ensures send_conf tr2 sender receiver payload)
  ;
  send_auth: tr:trace -> sender:principal -> payload:a -> prop;
  send_auth_later:
    tr1:trace -> tr2:trace ->
    sender:principal -> payload:a ->
    Lemma
    (requires
      send_auth tr1 sender payload /\
      is_well_formed a (bytes_well_formed tr1) payload /\
      tr1 <$ tr2
    )
    (ensures send_auth tr2 sender payload)
  ;
  send_conf_auth: tr:trace -> sender:principal -> receiver:principal -> payload:a -> prop;
  send_conf_auth_later:
    tr1:trace -> tr2:trace ->
    sender:principal -> receiver:principal -> payload:a ->
    Lemma
    (requires
      send_conf_auth tr1 sender receiver payload /\
      is_well_formed a (bytes_well_formed tr1) payload /\
      tr1 <$ tr2
    )
    (ensures send_conf_auth tr2 sender receiver payload)
}

let default_comm_higher_layer_event_preds (a:Type) {| parseable_serializeable bytes a |} : comm_higher_layer_event_preds a = {
  send_conf = (fun tr sender receiver payload -> False);
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ());
  send_auth = (fun tr sender payload -> False);
  send_auth_later = (fun tr1 tr2 sender payload -> ());
  send_conf_auth = (fun tr sender receiver payload -> False);
  send_conf_auth_later = (fun tr1 tr2 sender receiver payload -> ())
}

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer
  {|cinvs:crypto_invariants|}
  (#a:Type) {| parseable_serializeable bytes a |}
  (higher_layer_preds:comm_higher_layer_event_preds a) :
  event_predicate communication_event =
  fun tr prin e ->
    (match e with
    | CommConfSendMsg sender receiver payload -> (
      is_knowable_by (comm_label sender receiver) tr payload /\
      parse_and_pred (higher_layer_preds.send_conf tr sender receiver) payload
    )
    | CommConfReceiveMsg receiver payload -> (
      Some? (parse a payload) /\
      (
        (exists sender. event_triggered tr sender (CommConfSendMsg sender receiver payload)) \/
        is_publishable tr payload
      )
    )
    | CommAuthSendMsg sender payload -> (
      parse_and_pred (higher_layer_preds.send_auth tr sender) payload
    )
    | CommAuthReceiveMsg sender receiver payload -> (
      Some? (parse a payload) /\
      is_publishable tr payload /\
      (
        event_triggered tr sender (CommAuthSendMsg sender payload) \/
        is_corrupt tr (long_term_key_label sender)
      )
    )
    | CommConfAuthSendMsg sender receiver payload -> (
      is_knowable_by (comm_label sender receiver) tr payload /\
      parse_and_pred (higher_layer_preds.send_conf_auth tr sender receiver) payload
    )
    | CommConfAuthReceiveMsg sender receiver payload -> (
      // We can only show the following about the decrypted ciphertext (payload):
      // event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) \/
      // is_corrupt tr (long_term_key_label sender)
      //
      // This is because of the case where the ciphertext is created by an honest
      // user, but then intercepted, and the signed message, including sender
      // and receiver information, is created by the attacker.
      // Since the attacker can freely choose the sender/receiver information, the
      // receiver cannot guarantee that the full confidential/authenticated message
      // was honestly generated by the stated sender.
      Some? (parse a payload) /\
      (
        event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) \/
        is_corrupt tr (long_term_key_label sender)
      )
    )
    )
#pop-options

val event_predicate_communication_layer_and_tag:
  {|cinvs:crypto_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  comm_higher_layer_event_preds a ->
  (string & compiled_event_predicate)
let event_predicate_communication_layer_and_tag #cinvs higher_layer_preds =
  (event_communication_event.tag, compile_event_pred (event_predicate_communication_layer #cinvs higher_layer_preds))

val has_communication_layer_event_predicates:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  comm_higher_layer_event_preds a ->
  prop
let has_communication_layer_event_predicates #invs higher_layer_preds =
  has_event_pred (event_predicate_communication_layer #invs.crypto_invs higher_layer_preds)
