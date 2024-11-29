module DY.Lib.Communication.RequestResponse.Invariants

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

open DY.Lib.Communication.Core
open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.Core.Invariants

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** AEAD Predicate ***)

#push-options "--ifuel 1"
val aead_crypto_predicate_communication_layer: {|cusages:crypto_usages|} -> aead_crypto_predicate
let aead_crypto_predicate_communication_layer #cusages = {
  pred = (fun tr key_usage nonce msg ad ->
    (match parse response_message msg with
    | None -> False
    | Some {id; payload} -> (
      match parse authenticated_data ad with
      | None -> False
      | Some {client; server} -> (
          event_triggered tr server (CommServerSendResponse client server id payload) /\
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

val has_communication_layer_reqres_crypto_predicates:
  {|cinvs:crypto_invariants|} ->
  prop
let has_communication_layer_reqres_crypto_predicates #cinvs =
  // Fix for the get_label function in the model code
  cinvs.usages == default_crypto_usages /\
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
      is_secret (comm_label client server) tr key /\
      key `has_usage tr` (AeadKey comm_layer_aead_tag empty)
    )
    | ServerReceiveRequest {id; client; payload; key} -> (
      let server = prin in
      is_knowable_by (comm_label client server) tr key /\
      is_knowable_by (get_label tr key) tr payload /\
      is_knowable_by (get_label tr key) tr id /\
      (
        key `has_usage tr` (AeadKey comm_layer_aead_tag empty) \/
        is_publishable tr key
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
type comm_reqres_higher_layer_event_preds = {
  send_request: tr:trace -> client:principal -> server:principal -> payload:bytes -> key_label:label -> prop;
  send_request_later:
    tr1:trace -> tr2:trace ->
    client:principal -> server:principal -> payload:bytes -> key_label:label ->
    Lemma
    (requires
      send_request tr1 client server payload key_label /\
      bytes_well_formed tr1 payload /\
      tr1 <$ tr2
    )
    (ensures
      send_request tr2 client server payload key_label
    )
  ;
  send_response: tr:trace -> server:principal -> payload:bytes -> prop;
  send_response_later:
    tr1:trace -> tr2:trace ->
    server:principal -> payload:bytes ->
    Lemma
    (requires
      send_response tr1 server payload /\
      bytes_well_formed tr1 payload /\
      tr1 <$ tr2
    )
    (ensures
      send_response tr2 server payload
    )
}

val default_comm_reqres_higher_layer_event_preds: comm_reqres_higher_layer_event_preds
let default_comm_reqres_higher_layer_event_preds = {
  send_request = (fun tr client server payload key_label -> True);
  send_request_later = (fun tr1 tr2 client server payload key_label -> ());
  send_response = (fun tr server payload -> True);
  send_response_later = (fun tr1 tr2 server payload -> ())
}

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer_reqres
  {|cinvs:crypto_invariants|}
  (higher_layer_resreq_preds:comm_reqres_higher_layer_event_preds) : 
  event_predicate communication_reqres_event =
  fun tr prin e ->
    (match e with
    | CommClientSendRequest client server id payload key -> (
      is_knowable_by (get_label tr key) tr payload /\
      is_secret (comm_label client server) tr key /\
      is_secret (get_label tr key) tr id /\
      key `has_usage tr` (AeadKey comm_layer_aead_tag empty) /\
      higher_layer_resreq_preds.send_request tr client server payload (get_label tr key)
    )
    | CommServerReceiveRequest client server id payload key -> (
      is_knowable_by (comm_label client server) tr payload /\
      (event_triggered tr client (CommClientSendRequest client server id payload key) \/
        is_publishable tr payload)
    )
    | CommServerSendResponse client server id payload -> (
      higher_layer_resreq_preds.send_response tr server payload
    )
    | CommClientReceiveResponse client server id payload key -> (
      event_triggered tr server (CommServerSendResponse client server id payload) \/
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
    )
    )
#pop-options

// Additional event preconditions for the events from the core communication layer
#push-options "--fuel 0 --ifuel 1"
val request_response_event_preconditions: {|cinvs:crypto_invariants|} -> comm_higher_layer_event_preds
let request_response_event_preconditions #cinvs = {
  default_comm_higher_layer_event_preds with
  send_conf = (fun tr client server req_payload -> (
      match decode_request_message req_payload with
      | None -> False
      | Some {id; client=client'; payload; key} -> (
        client == client' /\
        //is_knowable_by (get_label tr key) tr id /\
        event_triggered tr client (CommClientSendRequest client server id payload key)
      )
    )
  );
  send_conf_later = (fun tr1 tr2 client server req_payload -> (
      parse_wf_lemma request_message (bytes_well_formed tr1) req_payload;
      ()
    )
  )
}
#pop-options

val event_predicate_communication_layer_reqres_and_tag: 
  {|cinvs:crypto_invariants|} ->
  comm_reqres_higher_layer_event_preds ->
  list (string & compiled_event_predicate)
let event_predicate_communication_layer_reqres_and_tag #cinvs higher_layer_resreq_preds =
  [
    event_predicate_communication_layer_and_tag request_response_event_preconditions;
    event_communication_reqres_event.tag, compile_event_pred (event_predicate_communication_layer_reqres #cinvs higher_layer_resreq_preds)
  ]

val has_communication_layer_reqres_event_predicates:
  {|protocol_invariants|} ->
  comm_higher_layer_event_preds ->
  comm_reqres_higher_layer_event_preds ->
  prop
let has_communication_layer_reqres_event_predicates #invs higher_layer_preds higher_layer_resreq_preds =
  has_event_pred (event_predicate_communication_layer #invs.crypto_invs higher_layer_preds) /\
  has_event_pred (event_predicate_communication_layer_reqres #invs.crypto_invs higher_layer_resreq_preds)
