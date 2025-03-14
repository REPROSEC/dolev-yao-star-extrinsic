module DY.Lib.Communication.RequestResponse.Properties

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Typed

open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains security properties that can be proven from the
/// communication layer guarantees.

(*** Authentication Security Properties ***)

val server_authentication:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace -> i:timestamp ->
  higher_layer_resreq_preds:comm_reqres_higher_layer_event_preds a ->
  client:principal -> server:principal -> response:bytes -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_resreq_preds /\
    event_triggered_at tr i client (CommClientReceiveResponse client server  response key)
  )
  (ensures
    (exists request. event_triggered (prefix tr i) server (CommServerSendResponse server request response)) \/
    is_corrupt (prefix tr i) (principal_label client) \/
    is_corrupt (prefix tr i) (principal_label server)
  )
let server_authentication #invs #a tr i higher_layer_resreq_preds client server response key = ()


(*** Secrecy Security Property ***)

val key_secrecy_client:
  {|protocol_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> request:bytes -> response:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_state_predicates /\
    attacker_knows tr key /\
    (
      (exists sid. state_was_set tr client sid (ClientSendRequest {server; request; key})) \/
      (exists sid. state_was_set tr client sid (ClientReceiveResponse {server; response; key}))
    )
  )
  (ensures
    is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let key_secrecy_client tr client server key request response =
  attacker_only_knows_publishable_values tr key;
  ()
