module DY.Lib.Communication.Properties

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PKI
open DY.Lib.State.Typed

open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants
open DY.Lib.Communication.Core.Lemmas

open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains experimental functions
/// that extract properties from the communication
/// API and make them available to a higher layer.
/// It is not used currently and does probably not
/// give meaning full properties.

val confidential_message_send:
  {|crypto_invariants|} ->
  tr:trace ->
  payload:bytes -> prop
let confidential_message_send tr payload =
  exists i pk nonce.
    let msg = encrypt_message payload pk nonce in
    event_at tr i (MsgSent msg) /\
    bytes_invariant tr msg

val confidential_message_sender_authentication:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  receiver:principal ->
  payload:bytes ->
  Lemma
  (requires
    trace_invariant tr  /\
    has_communication_layer_event_predicates higher_layer_preds /\
    event_triggered tr receiver (CommConfReceiveMsg receiver payload)
  )
  (ensures
    (exists sender. event_triggered tr sender (CommConfSendMsg sender receiver payload)) \/
    is_publishable tr payload
  )
let confidential_message_sender_authentication #invs tr hlp receiver payload = ()


(*** Request Response Pair Properties ***)

val server_authentication:
  {|protocol_invariants|} ->
  tr:trace -> i:timestamp ->
  higher_layer_resreq_preds:comm_reqres_higher_layer_event_preds ->
  client:principal -> server:principal -> id:bytes -> payload:bytes -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_resreq_preds /\
    event_triggered_at tr i client (CommClientReceiveResponse client server  id payload key)    
  )
  (ensures
    event_triggered (prefix tr i) server (CommServerSendResponse client server id payload) \/
    is_corrupt (prefix tr i) (principal_label client) \/ 
    is_corrupt (prefix tr i) (principal_label server)
  )
let server_authentication #invs tr i higher_layer_resreq_preds client server id payload key = ()

val key_secrecy_client:
  {|protocol_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  id:bytes -> key:bytes -> payload:bytes -> 
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_state_predicates /\
    attacker_knows tr key /\
    (
      (exists sid. state_was_set tr client sid (ClientSendRequest {id; server; payload; key})) \/
      (exists sid. state_was_set tr client sid (ClientReceiveResponse {id; server; payload; key}))
    )
  )
  (ensures
    is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let key_secrecy_client tr client server id key payload =
  attacker_only_knows_publishable_values tr key
