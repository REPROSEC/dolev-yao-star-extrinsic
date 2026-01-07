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

(*** Helper Predicates ***)

unfold
val comm_conf_send_event_triggered:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  trace -> principal -> principal -> a ->
  prop
let comm_conf_send_event_triggered #a tr sender receiver payload =
  event_triggered tr sender (CommConfSendMsg sender receiver payload <: communication_core_event a)

unfold
val comm_auth_send_event_triggered:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  trace -> principal -> a ->
  prop
let comm_auth_send_event_triggered #a tr sender payload =
  event_triggered tr sender (CommAuthSendMsg sender payload <: communication_core_event a)

unfold
val comm_conf_auth_send_event_triggered:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  trace -> principal -> principal -> a ->
  prop
let comm_conf_auth_send_event_triggered #a tr sender receiver payload =
  event_triggered tr sender (CommConfAuthSendMsg sender receiver payload <: communication_core_event a)

(*** PkEnc Predicates ***)

#push-options "--ifuel 1"
val pke_crypto_predicates_communication_layer_core: {|cusages:crypto_usages|} -> a:Type0 -> {|comm_layer_core_config a|} -> pke_crypto_predicate
let pke_crypto_predicates_communication_layer_core #cusages a #config  = {
  pred = (fun tr sk_usage pk msg ->
    (exists sender receiver.
      sk_usage == long_term_key_type_to_usage (LongTermPkeKey (comm_layer_pkenc_tag a))  receiver /\
      (get_label tr msg) `can_flow tr` (comm_label sender receiver) /\
      parse_and_pred (comm_conf_send_event_triggered #a tr sender receiver) msg
    )
    );
  pred_later = (fun tr1 tr2 sk_usage pk msg -> ());
}
#pop-options

val pke_crypto_predicates_and_tag_communication_layer_core:
  {|cusages:crypto_usages|} ->
  (a:Type0) -> {|comm_layer_core_config a|} ->
  (string & pke_crypto_predicate)
let pke_crypto_predicates_and_tag_communication_layer_core #cusages a #config =
  ((comm_layer_pkenc_tag a), pke_crypto_predicates_communication_layer_core a)

(*** Sign Predicates ***)

#push-options "--ifuel 3 --fuel 0"
val sign_crypto_predicate_communication_layer_core: {|cusages:crypto_usages|} -> a:Type0 -> {|comm_layer_core_config a|} -> sign_crypto_predicate
let sign_crypto_predicate_communication_layer_core #cusages a #config = {
  pred = (fun tr sk_usage vk sig_msg ->
    (match parse (signature_input a) sig_msg with
    | Some (Plain sender receiver payload) -> (
      sk_usage == long_term_key_type_to_usage (LongTermSigKey (comm_layer_sign_tag a)) sender /\
      get_label tr (serialize a payload) `can_flow tr` public /\
      comm_auth_send_event_triggered #a tr sender payload
    )
    | Some (Encrypted sender receiver payload pk_receiver) -> (
      get_label tr payload `can_flow tr` public /\
      sk_usage == long_term_key_type_to_usage (LongTermSigKey (comm_layer_sign_tag a)) sender /\
      (exists plain_payload nonce.
        payload == pke_enc pk_receiver nonce plain_payload /\
        parse_and_pred #a (comm_conf_auth_send_event_triggered tr sender receiver) plain_payload
      )
    )
    | None -> False)
  );
  pred_later = (fun tr1 tr2 sk_usage vk msg -> (
    parse_wf_lemma (signature_input a) (bytes_well_formed tr1) msg);
    match parse (signature_input a) msg with
    | Some (Plain sender receiver payload) -> (
      serialize_wf_lemma a (bytes_well_formed tr1) payload;
      ()
    )
    | Some (Encrypted _ _ _ _) -> ()
    | None -> assert(False)
  );
}
#pop-options

val sign_crypto_predicate_and_tag_communication_layer_core:
  {|cusages:crypto_usages|} ->
  (a:Type0) -> {|comm_layer_core_config a|} ->
  (string & sign_crypto_predicate)
let sign_crypto_predicate_and_tag_communication_layer_core #cusages a #config =
  (comm_layer_sign_tag a, sign_crypto_predicate_communication_layer_core a)

val has_communication_layer_core_crypto_predicates:
  {|crypto_invariants|} ->
  (a:Type0) -> {|comm_layer_core_config a|} ->
  prop
let has_communication_layer_core_crypto_predicates #cinvs a #config =
  has_pke_predicate (pke_crypto_predicates_and_tag_communication_layer_core a) /\
  has_sign_predicate (sign_crypto_predicate_and_tag_communication_layer_core a)

(*** Event Predicates ***)

noeq
type comm_core_higher_layer_event_preds (a:Type) {|comm_layer_core_config a|} = {
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

let default_comm_core_higher_layer_event_preds (a:Type) {|comm_layer_core_config a|} : comm_core_higher_layer_event_preds a = {
  send_conf = (fun tr sender receiver payload -> False);
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ());
  send_auth = (fun tr sender payload -> False);
  send_auth_later = (fun tr1 tr2 sender payload -> ());
  send_conf_auth = (fun tr sender receiver payload -> False);
  send_conf_auth_later = (fun tr1 tr2 sender receiver payload -> ())
}

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer_core
  {|cinvs:crypto_invariants|}
  (#a:Type0) {|comm_layer_core_config a|}
  (higher_layer_preds:comm_core_higher_layer_event_preds a) :
  event_predicate (communication_core_event a) =
  fun tr prin e ->
    (match e with
    | CommConfSendMsg sender receiver payload -> (
      is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
      higher_layer_preds.send_conf tr sender receiver payload
    )
    | CommConfReceiveMsg receiver payload -> (
      (exists sender. comm_conf_send_event_triggered #a tr sender receiver payload) \/
      is_well_formed a (is_publishable tr) payload
    )
    | CommAuthSendMsg sender payload -> (
      higher_layer_preds.send_auth tr sender payload
    )
    | CommAuthReceiveMsg sender receiver payload -> (
      is_well_formed a (is_publishable tr) payload /\
      (
        comm_auth_send_event_triggered #a tr sender payload \/
        is_corrupt tr (long_term_key_label sender)
      )
    )
    | CommConfAuthSendMsg sender receiver payload -> (
      is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
      higher_layer_preds.send_conf_auth tr sender receiver payload
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
      (
        comm_conf_auth_send_event_triggered #a tr sender receiver payload \/
        is_corrupt tr (long_term_key_label sender)
      )
    )
    )
#pop-options

val event_predicate_and_tag_communication_layer_core:
  {|cinvs:crypto_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  comm_core_higher_layer_event_preds a ->
  (string & compiled_event_predicate)
let event_predicate_and_tag_communication_layer_core #cinvs #a higher_layer_preds =
  mk_event_tag_and_pred (event_predicate_communication_layer_core higher_layer_preds)

val has_communication_layer_core_event_predicate:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  comm_core_higher_layer_event_preds a ->
  prop
let has_communication_layer_core_event_predicate #invs #a higher_layer_preds =
  has_event_pred (event_predicate_communication_layer_core higher_layer_preds)


(*** All Communication Layer Core Predicates ***)

val has_communication_layer_core_predicates:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  comm_core_higher_layer_event_preds a ->
  prop
let has_communication_layer_core_predicates #invs #a higher_layer_preds =
  has_communication_layer_core_crypto_predicates a /\
  has_communication_layer_core_event_predicate higher_layer_preds
