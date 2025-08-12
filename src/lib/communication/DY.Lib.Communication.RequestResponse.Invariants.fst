module DY.Lib.Communication.RequestResponse.Invariants

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Crypto.AEAD.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Tagged
open DY.Lib.State.Typed
open DY.Lib.Comparse.DYUtils

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.Core.Invariants

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** AEAD Predicate ***)

#push-options "--ifuel 1"
val aead_crypto_predicate_communication_layer:
  {|cusages:crypto_usages|} ->
  a:Type0 -> {|comm_layer_reqres_config a|} ->
  aead_crypto_predicate
let aead_crypto_predicate_communication_layer #cusages a #config = {
  pred = (fun tr key_usage key nonce msg ad ->
      (match parse authenticated_data ad with
      | None -> False
      | Some {server} -> (exists request.
        match parse a msg with
        | None -> False
        | Some response ->
          event_triggered tr server (CommServerSendResponse server request response <: communication_reqres_event a)
      )
    )
  );
  pred_later = (fun tr1 tr2 key_usage key nonce msg ad -> (
    parse_wf_lemma authenticated_data (bytes_well_formed tr1) ad;
    ()
  ))
}
#pop-options

val aead_crypto_predicates_communication_layer_reqres_and_tag:
  {|cusages:crypto_usages|} ->
  a:Type0 -> {|comm_layer_reqres_config a|} ->
  (string & aead_crypto_predicate)
let aead_crypto_predicates_communication_layer_reqres_and_tag #cusages a #config =
  (comm_layer_aead_tag a, aead_crypto_predicate_communication_layer a)


(*** Core Crypto Predicates ***)

val pke_crypto_predicates_communication_layer_reqres_and_tag:
  {|cusages:crypto_usages|} ->
  a:Type0 -> {|comm_layer_reqres_config a|} ->
  (string & pke_crypto_predicate)
let pke_crypto_predicates_communication_layer_reqres_and_tag #cusages a #config =
  pke_crypto_predicates_communication_layer_core_and_tag comm_message_t #(comm_layer_tag_core_config_reqres a)

val sign_crypto_predicates_communication_layer_reqres_and_tag:
  {|cusages:crypto_usages|} ->
  a:Type0 -> {|comm_layer_reqres_config a|} ->
  (string & sign_crypto_predicate)
let sign_crypto_predicates_communication_layer_reqres_and_tag #cusages a #config =
  sign_crypto_predicates_communication_layer_core_and_tag comm_message_t #(comm_layer_tag_core_config_reqres a)

val has_communication_layer_reqres_crypto_predicates:
  {|cinvs:crypto_invariants|} ->
  a:Type0 -> {|comm_layer_reqres_config a|} ->
  prop
let has_communication_layer_reqres_crypto_predicates #cinvs a #config =
  // Fix for the get_label function in the model code
  cinvs.usages == default_crypto_usages /\
  has_pke_predicate (pke_crypto_predicates_communication_layer_reqres_and_tag a) /\
  has_sign_predicate (sign_crypto_predicates_communication_layer_reqres_and_tag a) /\
  has_aead_predicate (aead_crypto_predicates_communication_layer_reqres_and_tag a)


(*** State Predicates ***)

#push-options "--ifuel 2 --z3rlimit 10"
let state_predicates_communication_layer {|crypto_invariants|} (a:Type) {|comm_layer_reqres_config a|}: local_state_predicate (communication_states a) = {
  pred = (fun tr prin sess_id st ->
    match st with
    | ClientSendRequest {server; request; key} -> (
      let client = prin in
      is_well_formed a (is_knowable_by (comm_label client server) tr) request /\
      is_secret (comm_label client server) tr key /\
      key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty)
    )
    | ServerReceiveRequest {request; key} -> (
      let server = prin in
      is_knowable_by (principal_label server) tr key /\
      is_well_formed a (is_knowable_by (principal_label server) tr) request /\
      key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty)
    )
    | ClientReceiveResponse {server; response; key} -> (
      let client = prin in
      is_well_formed a (is_knowable_by (comm_label client server) tr) response /\
      is_secret (comm_label client server) tr key
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> (
    match st with
    | ClientSendRequest {server; request; key} ->
      assert(is_well_formed a (is_knowable_by (principal_typed_state_content_label prin (DY.Lib.State.Typed.tag #(communication_states a)) sess_id st) tr) request)
    | ServerReceiveRequest {request; key} ->
      assert(is_well_formed a (is_knowable_by (principal_typed_state_content_label prin (DY.Lib.State.Typed.tag #(communication_states a)) sess_id st) tr) request)
    | ClientReceiveResponse {server; response; key} ->
      assert(is_well_formed a (is_knowable_by (principal_typed_state_content_label prin (DY.Lib.State.Typed.tag #(communication_states a)) sess_id st) tr) response)
  ));
}
#pop-options

val state_predicates_communication_layer_reqres_and_tag:
  {|crypto_invariants|} ->
  (a:Type0) -> {|comm_layer_reqres_config a|} ->
  dtuple2 string local_bytes_state_predicate
let state_predicates_communication_layer_reqres_and_tag #cinvs a #config =
  mk_local_state_tag_and_pred (state_predicates_communication_layer a)

val state_update_predicates_communication_layer_and_tag:
  {|crypto_invariants|} ->
  (a:Type0) -> {|comm_layer_reqres_config a|} ->
  dtuple2 string local_bytes_state_update_predicate
let state_update_predicates_communication_layer_and_tag #cinvs a #config =
  mk_local_state_tag_and_update_pred (default_local_state_update_pred (communication_states a))

val has_communication_layer_reqres_state_predicates:
  {|protocol_invariants|} ->
  (a:Type0) -> {|comm_layer_reqres_config a|} ->
  prop
let has_communication_layer_reqres_state_predicates #invs a #config =
  has_local_state_predicate (state_predicates_communication_layer a) /\
  has_local_state_update_predicate (default_local_state_update_pred (communication_states a))

(*** Event Predicates ***)

noeq
type comm_reqres_higher_layer_event_preds (a:Type) {| comm_layer_reqres_config a |} = {
  send_request: tr:trace -> client:principal -> server:principal -> request:a -> key_label:label -> prop;
  send_request_later:
    tr1:trace -> tr2:trace ->
    client:principal -> server:principal -> request:a -> key_label:label ->
    Lemma
    (requires
      send_request tr1 client server request key_label /\
      is_well_formed a (bytes_well_formed tr1) request /\
      tr1 <$ tr2
    )
    (ensures
      send_request tr2 client server request key_label
    )
  ;
  send_response: tr:trace -> server:principal -> request:a -> response:a -> prop;
  send_response_later:
    tr1:trace -> tr2:trace ->
    server:principal -> request:a -> response:a ->
    Lemma
    (requires
      send_response tr1 server request response /\
      is_well_formed a (bytes_well_formed tr1) request /\
      is_well_formed a (bytes_well_formed tr1) response /\
      tr1 <$ tr2
    )
    (ensures
      send_response tr2 server request response
    )
}

let default_comm_reqres_higher_layer_event_preds (a:Type) {| comm_layer_reqres_config a |} : comm_reqres_higher_layer_event_preds a = {
  send_request = (fun tr client server request key_label -> True);
  send_request_later = (fun tr1 tr2 client server request key_label -> ());
  send_response = (fun tr server request response -> True);
  send_response_later = (fun tr1 tr2 server request response -> ())
}

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer_reqres
  {|crypto_invariants|}
  (#a:Type) {| comm_layer_reqres_config a |}
  (higher_layer_resreq_preds:comm_reqres_higher_layer_event_preds a) :
  event_predicate (communication_reqres_event a) =
  fun tr prin e ->
    (match e with
    | CommClientSendRequest client server request key -> (
      is_well_formed a (is_knowable_by (get_label tr key) tr) request /\
      is_secret (comm_label client server) tr key /\
      key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\
      higher_layer_resreq_preds.send_request tr client server request (get_label tr key)
    )
    | CommServerReceiveRequest server request key -> (
      is_knowable_by (principal_label server) tr key /\
      is_well_formed a (is_knowable_by (get_label tr key) tr) request /\
      key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\
      (
        (exists client. event_triggered tr client (CommClientSendRequest client server request key <: communication_reqres_event a)) \/
        is_publishable tr key
      )
    )
    | CommServerSendResponse server request response -> higher_layer_resreq_preds.send_response tr server request response
    | CommClientReceiveResponse client server response key -> (
      (exists request. event_triggered tr server (CommServerSendResponse server request response <: communication_reqres_event a)) \/
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
    )
    )
#pop-options

// Additional event preconditions for the events from the core communication layer
#push-options "--fuel 0 --ifuel 2"
val comm_core_higher_layer_event_preds_reqres:
  {|cinvs:crypto_invariants|} ->
  (a:Type0) -> {|comm_layer_reqres_config a|} ->
  comm_core_higher_layer_event_preds comm_message_t #(comm_layer_tag_core_config_reqres a)
let comm_core_higher_layer_event_preds_reqres #cinvs a #config = {
  (default_comm_core_higher_layer_event_preds comm_message_t #(comm_layer_tag_core_config_reqres a)) with
  send_conf = (fun tr client server (com_msg_t:comm_message_t) ->
    match com_msg_t with
    | RequestMessage {request; key} -> (
      match parse a request with
      | None -> False
      | Some request_parsed -> event_triggered tr client (CommClientSendRequest client server request_parsed key <: communication_reqres_event a)
    )
    | _ -> False
  );
  send_conf_later = (fun tr1 tr2 client server msg -> ()
  )
}
#pop-options

val event_predicate_communication_layer_reqres_and_tag:
  {|cinvs:crypto_invariants|} ->
  #a:Type0 -> {| comm_layer_reqres_config a |} ->
  comm_reqres_higher_layer_event_preds a ->
  list (string & compiled_event_predicate)
let event_predicate_communication_layer_reqres_and_tag #cinvs #a higher_layer_resreq_preds =
  [
    event_predicate_communication_layer_core_and_tag (comm_core_higher_layer_event_preds_reqres a);
    mk_event_tag_and_pred (event_predicate_communication_layer_reqres higher_layer_resreq_preds)
  ]

val has_communication_layer_reqres_event_predicates:
  {|protocol_invariants|} ->
  #a:Type0 -> {| comm_layer_reqres_config a |} ->
  comm_reqres_higher_layer_event_preds a ->
  prop
let has_communication_layer_reqres_event_predicates #invs #a #config higher_layer_resreq_preds =
  has_event_pred (event_predicate_communication_layer_core (comm_core_higher_layer_event_preds_reqres a)) /\
  has_event_pred (event_predicate_communication_layer_reqres higher_layer_resreq_preds)
