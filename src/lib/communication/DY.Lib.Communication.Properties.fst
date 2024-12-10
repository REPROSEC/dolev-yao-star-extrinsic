module DY.Lib.Communication.Properties

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Typed

open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants
open DY.Lib.Communication.Core.Lemmas

open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains security properties that can be proven from the
/// communication layer guarantees.

(*** Authenticated Messages Properties ***)

val sender_authentication:
  {|protocol_invariants|} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  sender:principal -> receiver:principal ->
  payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_event_predicates higher_layer_preds /\
    event_triggered_at tr i receiver (CommAuthReceiveMsg sender receiver payload)
  )
  (ensures
    event_triggered (prefix tr i) sender (CommAuthSendMsg sender payload) \/
    is_corrupt (prefix tr i) (long_term_key_label sender)
  )
let sender_authentication tr i higher_layer_preds sender receiver secret = ()


(*** Confidential and Authenticated Messages Properties ***)

val sender_confauth_authentication:
  {|protocol_invariants|} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  sender:principal -> receiver:principal ->
  payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_event_predicates higher_layer_preds /\
    event_triggered_at tr i receiver (CommConfAuthReceiveMsg sender receiver payload)
  )
  (ensures
    event_triggered tr sender (CommConfAuthSendMsg sender receiver payload) \/
    is_corrupt tr (long_term_key_label sender)
  )
let sender_confauth_authentication tr i higher_layer_preds sender receiver secret = ()


(*** Request Response Pair Properties ***)

val server_authentication:
  {|protocol_invariants|} ->
  tr:trace -> i:timestamp ->
  higher_layer_resreq_preds:comm_reqres_higher_layer_event_preds ->
  client:principal -> server:principal -> payload:bytes -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_resreq_preds /\
    event_triggered_at tr i client (CommClientReceiveResponse client server  payload key)    
  )
  (ensures
    event_triggered (prefix tr i) server (CommServerSendResponse server payload) \/
    is_corrupt (prefix tr i) (principal_label client) \/ 
    is_corrupt (prefix tr i) (principal_label server)
  )
let server_authentication #invs tr i higher_layer_resreq_preds client server payload key = ()

val key_secrecy_client:
  {|protocol_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> payload:bytes -> 
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_state_predicates /\
    attacker_knows tr key /\
    (
      (exists sid. state_was_set tr client sid (ClientSendRequest {server; payload; key})) \/
      (exists sid. state_was_set tr client sid (ClientReceiveResponse {server; payload; key}))
    )
  )
  (ensures
    is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let key_secrecy_client tr client server key payload =
  attacker_only_knows_publishable_values tr key;
  ()
