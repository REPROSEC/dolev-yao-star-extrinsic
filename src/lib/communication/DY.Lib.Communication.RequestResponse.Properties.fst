module DY.Lib.Communication.RequestResponse.Properties

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Typed

open DY.Lib.Communication.Data
open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains security properties that can be proven from the
/// communication layer guarantees.

(*** Authentication Security Properties ***)

val server_authentication:
  {|protocol_invariants|} ->
  #a:Type -> {| comm_layer_reqres_config a |} ->
  tr:trace -> i:timestamp ->
  higher_layer_resreq_preds:comm_reqres_higher_layer_event_preds a ->
  client:principal -> server:principal -> response:a -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_event_predicates higher_layer_resreq_preds /\
    event_triggered_at tr i client (CommClientReceiveResponse client server  response key <: communication_reqres_event a)
  )
  (ensures
    (exists request. event_triggered (prefix tr i) server (CommServerSendResponse server request response key <: communication_reqres_event a)) \/
    is_corrupt (prefix tr i) (principal_label client) \/
    is_corrupt (prefix tr i) (principal_label server)
  )
let server_authentication #tag #invs #a tr i higher_layer_resreq_preds client server response key = ()


(*** Secrecy Security Property ***)

val key_secrecy_client:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> request:a -> response:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_state_predicate a /\
    attacker_knows tr key /\
    (
      (exists sid. state_was_set tr client sid (ClientSendRequest {server; request; key} <: communication_states a)) \/
      (exists sid. state_was_set tr client sid (ClientReceiveResponse {server; response; key} <: communication_states a))
    )
  )
  (ensures
    is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let key_secrecy_client #tag #invs tr client server key request response =
  attacker_only_knows_publishable_values tr key;
  ()

(*** Properties ***)

val request_message_properties:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds a ->
  server:principal -> key:bytes -> request:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates higher_layer_preds /\
    event_triggered_at tr i server (CommServerReceiveRequest server request key <: communication_reqres_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (principal_label server) (prefix tr i)) request /\
    (exists client. higher_layer_preds.send_request (prefix tr i) client server request (get_label (prefix tr i) key)) \/
    is_publishable (prefix tr i) key
  )
let request_message_properties #invs #a tr i higher_layer_preds server key request =
  let send_event client:communication_reqres_event a = CommClientSendRequest client server request key in
  let tr_i = prefix tr i in
  let key_label = get_label tr_i key in
  assert(is_well_formed a (is_knowable_by (principal_label server) tr_i) request);
  assert(exists client. event_triggered tr_i client (send_event client) \/
            is_publishable tr_i key);
  eliminate (exists client. event_triggered tr_i client (send_event client)) \/
            is_publishable tr_i key
  returns
    is_well_formed a (is_knowable_by (principal_label server) tr_i) request /\
    (exists client. higher_layer_preds.send_request (prefix tr i) client server request key_label) \/
    is_publishable tr_i key
  with _. eliminate exists client. event_triggered tr_i client (send_event client)
    returns _
    with _. (
      let j = find_event_triggered_at_timestamp tr client (send_event client) in
      find_event_triggered_at_timestamp_later tr_i tr client (send_event client);

      higher_layer_preds.send_request_later (prefix tr j) tr_i client server request key_label;
      ()
    )
  and _. ()
