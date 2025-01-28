module DY.Lib.Communication.Core.Properties

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

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains security properties that can be proven from the
/// communication layer guarantees.

(*** Authenticated Messages Properties ***)

val sender_authentication:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_higher_layer_event_preds a ->
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
let sender_authentication #invs #a tr i higher_layer_preds sender receiver secret = ()


(*** Confidential and Authenticated Messages Properties ***)

val sender_confauth_authentication:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_higher_layer_event_preds a ->
  sender:principal -> receiver:principal ->
  payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_event_predicates higher_layer_preds /\
    event_triggered_at tr i receiver (CommConfAuthReceiveMsg sender receiver payload)
  )
  (ensures
    event_triggered (prefix tr i) sender (CommConfAuthSendMsg sender receiver payload) \/
    is_corrupt (prefix tr i) (long_term_key_label sender)
  )
let sender_confauth_authentication #invs #a tr i higher_layer_preds sender receiver secret = ()
