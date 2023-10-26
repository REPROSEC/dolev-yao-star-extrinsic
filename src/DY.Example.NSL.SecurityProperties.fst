module DY.Example.NSL.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total.Proof
open DY.Example.NSL.Protocol.Stateful
open DY.Example.NSL.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

val initiator_authentication:
  tr:trace -> i:nat ->
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    event_triggered_at tr i bob nsl_event_label (serialize nsl_event (Respond2 alice bob n_a n_b)) /\
    trace_invariant nsl_protocol_invs tr
  )
  (ensures
    principal_corrupt tr alice \/ principal_corrupt tr bob \/
    event_triggered (prefix tr i) alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b))
  )
let initiator_authentication tr i alice bob n_a n_b = ()

val responder_authentication:
  tr:trace -> i:nat ->
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    event_triggered_at tr i alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b)) /\
    trace_invariant nsl_protocol_invs tr
  )
  (ensures
    principal_corrupt tr alice \/ principal_corrupt tr bob \/
    event_triggered (prefix tr i) bob nsl_event_label (serialize nsl_event (Respond1 alice bob n_a n_b))
  )
let responder_authentication tr i alice bob n_a n_b = ()

val n_a_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes ->
  Lemma
  (requires
    attacker_knows tr n_a /\
    trace_invariant nsl_protocol_invs tr /\ (
      (exists sess_id. typed_state_was_set tr nsl_session_label alice sess_id (InitiatorSentMsg1 bob n_a <: nsl_session)) \/
      (exists sess_id n_b. typed_state_was_set tr nsl_session_label alice sess_id (InitiatorSentMsg3 bob n_a n_b <: nsl_session)) \/
      (exists sess_id n_b. typed_state_was_set tr nsl_session_label bob sess_id (ResponderReceivedMsg3 alice n_a n_b <: nsl_session))
    )
  )
  (ensures principal_corrupt tr alice \/ principal_corrupt tr bob)
let n_a_secrecy tr alice bob n_a =
  attacker_only_knows_publishable_values nsl_protocol_invs tr n_a

val n_b_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_b:bytes ->
  Lemma
  (requires
    attacker_knows tr n_b /\
    trace_invariant nsl_protocol_invs tr /\ (
      (exists sess_id n_a. typed_state_was_set tr nsl_session_label bob sess_id (ResponderSentMsg2 alice n_a n_b <: nsl_session)) \/
      (exists sess_id n_a. typed_state_was_set tr nsl_session_label bob sess_id (ResponderReceivedMsg3 alice n_a n_b <: nsl_session)) \/
      (exists sess_id n_a. typed_state_was_set tr nsl_session_label alice sess_id (InitiatorSentMsg3 bob n_a n_b <: nsl_session))
    )
  )
  (ensures principal_corrupt tr alice \/ principal_corrupt tr bob)
let n_b_secrecy tr alice bob n_b =
  attacker_only_knows_publishable_values nsl_protocol_invs tr n_b
