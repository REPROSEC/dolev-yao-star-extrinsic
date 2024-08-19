module DY.Lib.Communication.API.Properties

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PKI

open DY.Lib.Communication.API
open DY.Lib.Communication.API.Predicates

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains experimental functions
/// that extract properties from the communication
/// API and make them available to a higher layer.
/// It is not used currently and does probably not
/// give meaning full properties.

val confidential_message_send:
  {|crypto_invariants|} ->
  tr:trace ->
  sender:principal -> receiver:principal ->
  payload:bytes -> prop
let confidential_message_send tr sender receiver payload =
  exists i pk nonce.
    let msg = encrypt_message sender receiver payload pk nonce in
    event_at tr i (MsgSent msg) /\
    bytes_invariant tr msg

val confidential_message_sender_authentication:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  higher_layer_preds:comm_higher_layer_event_preds ->
  sender:principal -> receiver:principal ->
  payload:bytes ->
  Lemma
  (requires
    trace_invariant tr  /\
    has_communication_layer_event_predicates invs higher_layer_preds /\
    event_triggered tr receiver (CommConfReceiveMsg sender receiver payload)
  )
  (ensures
    event_triggered tr sender (CommConfSendMsg sender receiver payload) \/
    is_publishable tr payload
  )
let confidential_message_sender_authentication #invs tr hlp sender receiver payload = ()
