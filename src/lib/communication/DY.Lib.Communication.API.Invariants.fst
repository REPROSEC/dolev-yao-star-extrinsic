module DY.Lib.Communication.API.Invariants

open Comparse
open DY.Core
open DY.Lib.Communication.Core.Extension
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Crypto.AEAD.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Tagged
open DY.Lib.State.Typed

open DY.Lib.Communication.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** PkEnc Predicates ***)

val pkenc_crypto_predicates_communication_layer: {|cusages:crypto_usages|} -> pkenc_crypto_predicate
let pkenc_crypto_predicates_communication_layer #cusages = {
  pred = (fun tr sk_usage msg ->
    (exists sender receiver.
      sk_usage == long_term_key_type_to_usage (LongTermPkEncKey comm_layer_pkenc_tag)  receiver /\
      (get_label tr msg) `can_flow tr` (join (principal_label sender) (principal_label receiver)) /\
      event_triggered tr sender (CommConfSendMsg sender receiver msg)
    ));
  pred_later = (fun tr1 tr2 pk msg -> ());
}

val pkenc_crypto_predicates_communication_layer_and_tag: 
  {|cusages:crypto_usages|} ->
  (string & pkenc_crypto_predicate)
let pkenc_crypto_predicates_communication_layer_and_tag #cusages = 
  (comm_layer_pkenc_tag, pkenc_crypto_predicates_communication_layer)

(*** AEAD Predicate ***)

#push-options "--ifuel 1 --fuel 0"
val aead_crypto_predicate_communication_layer: {|cusages:crypto_usages|} -> aead_crypto_predicate
let aead_crypto_predicate_communication_layer #cusages = {
  pred = (fun tr key_usage nonce msg ad ->
    (match parse response_message msg with
    | None -> False
    | Some {id; payload} -> (
      match parse authenticated_data ad with
      | None -> False
      | Some {client; server} -> (
        event_triggered tr server (CommServerReceiveRequest server id payload) /\
        (get_label tr id) `can_flow tr` (comm_label client server) /\
        (get_label tr payload) `can_flow tr` (comm_label client server)
      )
    ))
  );
  pred_later = (fun tr1 tr2 key_usage nonce msg ad -> (
    parse_wf_lemma response_message (bytes_well_formed tr1) msg;
    parse_wf_lemma authenticated_data (bytes_well_formed tr1) ad;
    ()
  ))
}
#pop-options

val aead_crypto_predicates_communication_layer_and_tag:
  {|cusages:crypto_usages|} ->
  (string & aead_crypto_predicate)
let aead_crypto_predicates_communication_layer_and_tag #cusages =
  (comm_layer_aead_tag, aead_crypto_predicate_communication_layer)

(*** Sign Predicates ***)

#push-options "--ifuel 3 --fuel 0"
val sign_crypto_predicates_communication_layer: {|cusages:crypto_usages|} -> sign_crypto_predicate
let sign_crypto_predicates_communication_layer #cusages = {
  pred = (fun tr sk_usage sig_msg ->
    (match parse signature_input sig_msg with
    | Some (Plain {sender; receiver; payload}) -> (
      sk_usage == long_term_key_type_to_usage (LongTermSigKey comm_layer_sign_tag) sender /\
      get_label tr payload `can_flow tr` public /\
      event_triggered tr sender (CommAuthSendMsg sender payload)
    )
    | Some (Encrypted {sender; receiver; payload=enc_payload}) -> (
      match pk_enc_extract_msg enc_payload with
      | None -> False
      | Some plain_payload -> (
        sk_usage == long_term_key_type_to_usage (LongTermSigKey comm_layer_sign_tag) sender /\     
        get_label tr enc_payload `can_flow tr` public /\
        event_triggered tr sender (CommConfAuthSendMsg sender receiver plain_payload)
      )
    )
    | None -> False)
  );
  pred_later = (fun tr1 tr2 vk msg ->  parse_wf_lemma signature_input (bytes_well_formed tr1) msg);
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
  has_sign_predicate sign_crypto_predicates_communication_layer_and_tag /\
  has_aead_predicate aead_crypto_predicates_communication_layer_and_tag


(*** State Predicates ***)

#push-options "--ifuel 2 --z3rlimit 25"
let state_predicates_communication_layer {|crypto_invariants|}: local_state_predicate communication_states = {
  pred = (fun tr prin sess_id st -> 
    match st with
    | ClientSendRequest {id; server; payload; key} -> (
      let client = prin in
      is_secret (comm_label client server) tr id /\
      is_knowable_by (comm_label client server) tr payload /\
      is_secret (comm_label client server) tr key
    )
    | ServerReceiveRequest {id; client; payload; key} -> (
      let server = prin in
      (exists client.
        is_knowable_by (comm_label client server) tr id /\
        is_knowable_by (comm_label client server) tr payload /\
        is_knowable_by (comm_label client server) tr key
      )
    )
    | ClientReceiveResponse {id; server; payload; key} -> (
      let client = prin in
      is_secret (comm_label client server) tr id /\
      is_knowable_by (comm_label client server) tr payload /\
      is_secret (comm_label client server) tr key
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id state -> ());
  pred_knowable = (fun tr prin sess_id state -> ());
}
#pop-options

val state_predicates_communication_layer_and_tag: 
  {|crypto_invariants|} ->
  dtuple2 string local_bytes_state_predicate
let state_predicates_communication_layer_and_tag #cinvs =
  (|local_state_communication_layer_session.tag, local_state_predicate_to_local_bytes_state_predicate (state_predicates_communication_layer #cinvs)|)

val has_communication_layer_state_predicates:
  {|protocol_invariants|} ->
  prop
let has_communication_layer_state_predicates #invs =
  has_local_state_predicate state_predicates_communication_layer
 

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
      tr1 <$ tr2
    )
    (ensures send_conf_auth tr2 sender receiver payload)
  ;
  send_request: tr:trace -> client:principal -> server:principal -> payload:bytes -> prop;
  send_request_later:
    tr1:trace -> tr2:trace ->
    client:principal -> server:principal -> payload:bytes ->
    Lemma
    (requires
      send_request tr1 client server payload /\
      tr1 <$ tr2
    )
    (ensures
      send_request tr2 client server payload
    )
  ;
  send_response: tr:trace -> server:principal -> payload:bytes -> prop;
  send_response_later:
    tr1:trace -> tr2:trace ->
    server:principal -> payload:bytes ->
    Lemma
    (requires
      send_response tr1 server payload /\
      tr1 <$ tr2
    )
    (ensures
      send_response tr2 server payload
    )
}

val default_comm_higher_layer_event_preds: comm_higher_layer_event_preds
let default_comm_higher_layer_event_preds = {
  send_conf = (fun tr sender receiver payload -> True);
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ());
  send_auth = (fun tr sender payload -> True);
  send_auth_later = (fun tr1 tr2 sender payload -> ());
  send_conf_auth = (fun tr sender receiver payload -> True);
  send_conf_auth_later = (fun tr1 tr2 sender receiver payload -> ());
  send_request = (fun tr client server payload -> True);
  send_request_later = (fun tr1 tr2 client server payload -> ());
  send_response = (fun tr server payload -> True);
  send_response_later = (fun tr1 tr2 server payload -> ())
}

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer 
  {|cinvs:crypto_invariants|}
  (local_extension:comm_higher_layer_event_preds)
  (higher_layer_preds:comm_higher_layer_event_preds) : 
  event_predicate communication_event =
  fun tr prin e ->
    (match e with
    | CommConfSendMsg sender receiver payload -> (
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr payload /\
      higher_layer_preds.send_conf tr sender receiver payload /\
      local_extension.send_conf tr sender receiver payload
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
        (
          event_triggered tr sender (CommAuthSendMsg sender payload)
        ) \/
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
    | CommClientSendRequest client server id payload -> (
      is_knowable_by (comm_label client server) tr payload /\
      higher_layer_preds.send_request tr client server payload
    )
    | CommServerReceiveRequest server id payload -> (
      exists client. is_knowable_by (comm_label client server) tr payload /\
      (event_triggered tr client (CommClientSendRequest client server id payload) \/
        is_publishable tr payload)
    )
    | CommServerSendResponse server id payload -> (
      (exists client. is_knowable_by (comm_label client server) tr payload) /\
      higher_layer_preds.send_response tr server payload
    )
    | CommClientReceiveResponse client server id payload key -> (
      event_triggered tr server (CommServerReceiveRequest server id payload) \/
      is_corrupt tr (long_term_key_label server)
    )
    )
#pop-options

val event_predicate_communication_layer_and_tag: 
  {|cinvs:crypto_invariants|} ->
  comm_higher_layer_event_preds ->
  comm_higher_layer_event_preds ->
  (string & compiled_event_predicate)
let event_predicate_communication_layer_and_tag #cinvs local_extension higher_layer_preds =
  (event_communication_event.tag, compile_event_pred #communication_event (event_predicate_communication_layer #cinvs local_extension higher_layer_preds))

val has_communication_layer_event_predicates:
  {|protocol_invariants|} ->
  comm_higher_layer_event_preds ->
  comm_higher_layer_event_preds ->
  prop
let has_communication_layer_event_predicates #invs local_extension higher_layer_preds =
  has_event_pred (event_predicate_communication_layer local_extension higher_layer_preds)
