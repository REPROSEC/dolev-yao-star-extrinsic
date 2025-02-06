module DY.Lib.Communication.Core.Properties

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Typed
open DY.Lib.Comparse.DYUtils

open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants
open DY.Lib.Communication.Core.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains security properties that can be proven from the
/// communication layer guarantees.

(*** Confidential Messages Properties ***)

val conf_message_secrecy:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_higher_layer_event_preds a ->
  receiver:principal ->
  payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_event_predicates higher_layer_preds /\
    event_triggered_at tr i receiver (CommConfReceiveMsg receiver payload)
  )
  (ensures
    is_knowable_by (principal_label receiver) (prefix tr i) payload /\

    parse_and_pred (fun payload_parsed ->
      (exists sender. higher_layer_preds.send_conf (prefix tr i) sender receiver payload_parsed) \/
      is_well_formed a (is_publishable (prefix tr i)) payload_parsed
    ) payload
  )
let conf_message_secrecy #invs #a tr i higher_layer_preds receiver payload =
  let send_event sender = CommConfSendMsg sender receiver payload in
  let tr_i = prefix tr i in
  eliminate (exists sender. event_triggered tr_i sender (send_event sender)) \/
            is_publishable tr_i payload
  returns
    is_knowable_by (principal_label receiver) tr_i payload /\
    parse_and_pred (fun payload_parsed ->
      (exists sender. higher_layer_preds.send_conf (prefix tr i) sender receiver payload_parsed) \/
      is_well_formed a (is_publishable (prefix tr i)) payload_parsed
    ) payload
  with _. eliminate exists sender. event_triggered tr_i sender (send_event sender)
    returns _
    with _. (
      let j = find_event_triggered_at_timestamp tr sender (send_event sender) in
      find_event_triggered_at_timestamp_later tr_i tr sender (send_event sender);

      serialize_parse_inv_lemma a payload;
      higher_layer_preds.send_conf_later (prefix tr j) tr_i sender receiver (Some?.v (parse a payload))
    )
  and _. parse_wf_lemma a (is_publishable (prefix tr i)) payload


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
