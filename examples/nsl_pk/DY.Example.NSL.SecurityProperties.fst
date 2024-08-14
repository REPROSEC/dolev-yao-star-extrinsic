module DY.Example.NSL.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total.Proof
open DY.Example.NSL.Protocol.Stateful
open DY.Example.NSL.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module defines the security properties of the NSL protocol.
/// They are all implied by the protocol invariants,
/// defined in DY.Example.NSL.Protocol.Total.Proof
/// and DY.Example.NSL.Protocol.Stateful.Proof.
/// Because all functions of the NSL protocol preserve the protocol invariants,
/// the attacker function also preserves the invariants.
/// Hence these security theorems hold on every trace obtainable by the attacker.

/// If Bob thinks he talks with Alice,
/// then Alice thinks she talk to Bob (with the same nonces),
/// unless the attacker corrupted Alice or Bob.

val initiator_authentication:
  tr:trace -> i:timestamp ->
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    event_triggered_at tr i bob (Respond2 alice bob n_a n_b) /\
    trace_invariant tr
  )
  (ensures
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
    event_triggered (prefix tr i) alice (Initiate2 alice bob n_a n_b)
  )
let initiator_authentication tr i alice bob n_a n_b = ()

/// If Alice thinks she talks with Bob,
/// then Bob thinks he talk to Alice (with the same nonces),
/// unless the attacker corrupted Alice or Bob.

val responder_authentication:
  tr:trace -> i:timestamp ->
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    event_triggered_at tr i alice (Initiate2 alice bob n_a n_b) /\
    trace_invariant tr
  )
  (ensures
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
    event_triggered (prefix tr i) bob (Respond1 alice bob n_a n_b)
  )
let responder_authentication tr i alice bob n_a n_b = ()

/// The nonce n_a is unknown to the attacker,
/// unless the attacker corrupted Alice or Bob.

val n_a_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes ->
  Lemma
  (requires
    attacker_knows tr n_a /\
    trace_invariant tr /\ (
      (exists sess_id. state_was_set tr alice sess_id (InitiatorSentMsg1 bob n_a)) \/
      (exists sess_id n_b. state_was_set tr alice sess_id (InitiatorSentMsg3 bob n_a n_b)) \/
      (exists sess_id n_b. state_was_set tr bob sess_id (ResponderReceivedMsg3 alice n_a n_b))
    )
  )
  (ensures is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob))
let n_a_secrecy tr alice bob n_a =
  attacker_only_knows_publishable_values tr n_a;
  assert((join (principal_label alice) (principal_label bob)) `can_flow tr` public)

/// The nonce n_b is unknown to the attacker,
/// unless the attacker corrupted Alice or Bob.

val n_b_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_b:bytes ->
  Lemma
  (requires
    attacker_knows tr n_b /\
    trace_invariant tr /\ (
      (exists sess_id n_a. state_was_set tr bob sess_id (ResponderSentMsg2 alice n_a n_b)) \/
      (exists sess_id n_a. state_was_set tr bob sess_id (ResponderReceivedMsg3 alice n_a n_b)) \/
      (exists sess_id n_a. state_was_set tr alice sess_id (InitiatorSentMsg3 bob n_a n_b))
    )
  )
  (ensures is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob))
let n_b_secrecy tr alice bob n_b =
  attacker_only_knows_publishable_values tr n_b;
  assert((join (principal_label alice) (principal_label bob)) `can_flow tr` public)
