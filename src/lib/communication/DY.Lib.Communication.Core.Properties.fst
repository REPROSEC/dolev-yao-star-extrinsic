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

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants
open DY.Lib.Communication.Core.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains security properties that can be proven from the
/// communication layer guarantees.

(*** Confidential Messages Properties ***)

val conf_message_properties:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  receiver:principal ->
  payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_core_predicates higher_layer_preds /\
    event_triggered tr receiver (CommConfReceiveMsg receiver payload <: communication_core_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (principal_label receiver) tr) payload /\
    ((exists sender. higher_layer_preds.send_conf tr sender receiver payload) \/
    is_well_formed a (is_publishable tr) payload)
  )
let conf_message_properties #invs #a tr higher_layer_preds receiver payload =
  let send_event sender:communication_core_event a = CommConfSendMsg sender receiver payload in
  let i = find_event_triggered_at_timestamp tr receiver (CommConfReceiveMsg receiver payload <: communication_core_event a) in
  let tr_i = prefix tr i in
  eliminate (exists sender. event_triggered tr_i sender (send_event sender)) \/
            is_well_formed a (is_publishable tr_i) payload
  returns
    is_well_formed a (is_knowable_by (principal_label receiver) tr) payload /\
    ((exists sender. higher_layer_preds.send_conf tr sender receiver payload) \/
    is_well_formed a (is_publishable tr) payload)
  with _. eliminate exists sender. event_triggered (prefix tr i) sender (send_event sender)
    returns _
    with _. (
      let j = find_event_triggered_at_timestamp tr sender (send_event sender) in
      find_event_triggered_at_timestamp_later tr_i tr sender (send_event sender);

      higher_layer_preds.send_conf_later (prefix tr j) tr sender receiver payload;
      ()
    )
  and _. ()


(*** Authenticated Messages Properties ***)

val sender_authentication:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  sender:principal -> receiver:principal ->
  payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_core_predicates higher_layer_preds /\
    event_triggered_at tr i receiver (CommAuthReceiveMsg sender receiver payload <: communication_core_event a)
  )
  (ensures
    event_triggered (prefix tr i) sender (CommAuthSendMsg sender receiver payload <: communication_core_event a) \/
    is_corrupt (prefix tr i) (long_term_key_label sender)
  )
let sender_authentication #invs #a tr i higher_layer_preds sender receiver payload = ()

val authenticated_message_properties:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  sender:principal -> receiver:principal ->
  payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_core_predicates higher_layer_preds /\
    event_triggered tr receiver (CommAuthReceiveMsg sender receiver payload <: communication_core_event a)
  )
  (ensures
    is_well_formed a (is_publishable tr) payload /\
    (higher_layer_preds.send_auth tr sender receiver payload \/
    is_corrupt tr (long_term_key_label sender))
  )
let authenticated_message_properties #invs #a tr higher_layer_preds sender receiver payload =
  let send_event:communication_core_event a = CommAuthSendMsg sender receiver payload in
  let i = find_event_triggered_at_timestamp tr receiver (CommAuthReceiveMsg sender receiver payload <: communication_core_event a) in
  let tr_i = prefix tr i in
  eliminate event_triggered tr_i sender send_event \/ is_corrupt tr_i (long_term_key_label sender)
  returns
    is_well_formed a (is_publishable tr) payload /\
    (higher_layer_preds.send_auth tr sender receiver payload \/
    is_corrupt tr (long_term_key_label sender))
  with _. (
    let j = find_event_triggered_at_timestamp tr sender send_event in
    find_event_triggered_at_timestamp_later tr_i tr sender send_event;
    
    higher_layer_preds.send_auth_later (prefix tr j) tr sender receiver payload;
    ()
  )
  and _. ()


(*** Confidential and Authenticated Messages Properties ***)

val sender_confauth_authentication:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_core_config a|} ->
  tr:trace -> i:timestamp ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  sender:principal -> receiver:principal ->
  payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_core_predicates higher_layer_preds /\
    event_triggered_at tr i receiver (CommConfAuthReceiveMsg sender receiver payload <: communication_core_event a)
  )
  (ensures
    event_triggered (prefix tr i) sender (CommConfAuthSendMsg sender receiver payload <: communication_core_event a) \/
    is_corrupt (prefix tr i) (long_term_key_label sender)
  )
let sender_confauth_authentication #tag #invs #a tr i higher_layer_preds sender receiver secret = ()

val confauth_message_properties:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  sender:principal -> receiver:principal ->
  payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_core_predicates higher_layer_preds /\
    event_triggered tr receiver (CommConfAuthReceiveMsg sender receiver payload <: communication_core_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
    (higher_layer_preds.send_conf_auth tr sender receiver payload \/
    is_corrupt tr (long_term_key_label sender))
  )
let confauth_message_properties #invs #a tr higher_layer_preds sender receiver payload =
  let send_event:communication_core_event a = CommConfAuthSendMsg sender receiver payload in
  let i = find_event_triggered_at_timestamp tr receiver (CommConfAuthReceiveMsg sender receiver payload <: communication_core_event a) in
  let tr_i = prefix tr i in
  eliminate event_triggered tr_i sender send_event \/ is_corrupt tr_i (long_term_key_label sender)
  returns
    is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
    (higher_layer_preds.send_conf_auth tr sender receiver payload \/
    is_corrupt tr (long_term_key_label sender))
  with _. (
    let j = find_event_triggered_at_timestamp tr sender send_event in
    find_event_triggered_at_timestamp_later tr_i tr sender send_event;

    higher_layer_preds.send_conf_auth_later (prefix tr j) tr sender receiver payload;
    ()
  )
  and _. ()

val confauth_message_properties':
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_core_config a|} ->
  tr:trace ->
  higher_layer_preds:comm_core_higher_layer_event_preds a ->
  sender:principal -> receiver:principal -> payload:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_core_predicates higher_layer_preds /\
    event_triggered tr receiver (CommConfAuthReceiveMsg sender receiver payload <: communication_core_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
    (higher_layer_preds.send_conf_auth tr sender receiver payload \/
    is_well_formed a (is_publishable tr) payload)
  )
let confauth_message_properties' #invs #a tr higher_layer_preds sender receiver payload =
  let send_event:communication_core_event a = CommConfAuthSendMsg sender receiver payload in
  let i = find_event_triggered_at_timestamp tr receiver (CommConfAuthReceiveMsg sender receiver payload <: communication_core_event a) in
  let tr_i = prefix tr i in
  eliminate event_triggered tr_i sender send_event \/ is_well_formed a (is_publishable tr_i) payload
  returns
    is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload /\
    (higher_layer_preds.send_conf_auth tr sender receiver payload \/
    is_well_formed a (is_publishable tr) payload)
  with _. (
    let j = find_event_triggered_at_timestamp tr sender send_event in
    find_event_triggered_at_timestamp_later tr_i tr sender send_event;
    higher_layer_preds.send_conf_auth_later (prefix tr j) tr sender receiver payload;
    ()
  )
  and _. ()
  