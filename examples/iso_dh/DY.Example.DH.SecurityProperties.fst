module DY.Example.DH.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total.Proof
open DY.Example.DH.Protocol.Stateful
open DY.Example.DH.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"


(*** Authentication Properties ***)

val responder_authentication:
  tr:trace -> i:nat ->
  alice:principal -> bob:principal ->
  gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires 
    trace_invariant tr /\
    event_triggered_at tr i alice (Initiate2 alice bob gx gy k)
  )
  (ensures 
    is_corrupt tr (principal_label bob) \/
    (exists y. event_triggered (prefix tr i) bob (Respond1 alice bob gx gy y) /\
    k == dh y gx)
  )
let responder_authentication tr i alice bob gx gy k = ()

val initiator_authentication:
  tr:trace -> i:nat ->
  alice:principal -> bob:principal ->
  gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires 
    trace_invariant tr /\
    event_triggered_at tr i bob (Respond2 alice bob gx gy k)
  )
  (ensures 
    is_corrupt tr (principal_label alice) \/ 
    event_triggered (prefix tr i) alice (Initiate2 alice bob gx gy k)
  )
let initiator_authentication tr i alice bob gx gy k = ()

(*** Forward Secrecy Properties ***)

val initiator_forward_secrecy: 
  tr:trace -> alice:principal -> alice_si:state_id -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr alice alice_si (InitiatorSendMsg3 bob gx gy k) /\
    attacker_knows tr k
  )
  (ensures
    is_corrupt tr (principal_label bob) \/ is_corrupt tr (principal_state_label alice alice_si)
  )
let initiator_forward_secrecy tr alice alice_si bob gx gy k =
  attacker_only_knows_publishable_values tr k;

  // We derive the following fact from InitiatorSendMsg3 state invariant
  // and Respond1 event invariant
  // (this assert is not needed and only there for pedagogical purposes)
  assert(
    (exists x. gx == dh_pk x /\ k == dh x gy /\ is_secret (principal_state_label alice alice_si) tr x) /\
    (
      is_corrupt tr (principal_label bob) \/
      (exists y.
        (exists bob_si. is_secret (principal_state_label bob bob_si) tr y) /\
        gy = dh_pk y
      )
    )
  );

  // We can deduce from it the label of `k`, up to some corruption
  // (this assert is not needed and only there for pedagogical purposes)
  assert(
    is_corrupt tr (principal_label bob) \/
    (exists bob_si. get_label tr k `equivalent tr` join (principal_state_label alice alice_si) (principal_state_label bob bob_si))
  );

  // We deduce from the following this assertion,
  // that will trigger transitivity of `can_flow tr` from `join ...` to `get_label k` to `public`
  assert(
    is_corrupt tr (principal_label bob) \/
    (exists bob_si. join (principal_state_label alice alice_si) (principal_state_label bob bob_si) `can_flow tr` public)
  );

  // This assert allows to deduce corruption of principal bob from corruption state bob_si of principal bob
  assert(forall bob_si. principal_label bob `can_flow tr` principal_state_label bob bob_si);

  ()

val responder_forward_secrecy: 
  tr:trace -> alice:principal -> bob:principal -> bob_si:state_id -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr bob bob_si (ResponderReceivedMsg3 alice gx gy k) /\
    attacker_knows tr k
  )
  (ensures
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_state_label bob bob_si)
  )
let responder_forward_secrecy tr alice bob bob_si gx gy k = 
  attacker_only_knows_publishable_values tr k;

  // We derive the following fact from ResponderReceivedMsg3 state invariant
  // and Initiate2 event invariant
  // (this assert is not needed and only there for pedagogical purposes)
  assert(
    (exists y. gy == dh_pk y /\ k == dh y gx /\ is_secret (principal_state_label bob bob_si) tr y) /\
    (
      is_corrupt tr (principal_label alice) \/
      (exists x.
        (exists alice_si. is_secret (principal_state_label alice alice_si) tr x) /\
        k == dh x gy
      )
    )
  );

  // We can deduce from it the label of `k`, up to some corruption
  // (this assert is not needed and only there for pedagogical purposes)
  assert(
    is_corrupt tr (principal_label alice) \/
    (exists alice_si. get_label tr k `equivalent tr` join (principal_state_label alice alice_si) (principal_state_label bob bob_si))
  );

  // We deduce from the following this assertion,
  // that will trigger transitivity of `can_flow tr` from `join ...` to `get_label k` to `public`
  assert(
    is_corrupt tr (principal_label alice) \/
    (exists alice_si. join (principal_state_label alice alice_si) (principal_state_label bob bob_si) `can_flow tr` public)
  );

  // This assert is needed for the proof
  assert(exists alice_si. join (principal_state_label alice alice_si) (principal_state_label bob bob_si)
    `can_flow tr` public \/ 
    is_corrupt tr (principal_label alice));

  // This assert allows to deduce corruption of principal alice from corruption state alice_si of principal alice
  assert(forall alice_si. principal_label alice `can_flow tr` principal_state_label alice alice_si);

  ()
