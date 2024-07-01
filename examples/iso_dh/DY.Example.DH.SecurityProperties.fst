module DY.Example.DH.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total.Proof
open DY.Example.DH.Protocol.Stateful
open DY.Example.DH.Protocol.Stateful.Proof

#set-options "--fuel 8 --ifuel 8 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"


(*** Authentication Properties ***)

val initiator_authentication:
  tr:trace -> i:nat ->
  alice:principal -> bob:principal ->
  gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires 
    trace_invariant tr /\
    event_triggered_at tr i alice (Initiate2 alice bob gx gy k)
  )
  (ensures 
    (exists alice_si. is_corrupt tr (principal_state_label alice alice_si)) \/ 
    is_corrupt tr (principal_label bob) \/
    (exists y. event_triggered (prefix tr i) bob (Respond1 alice bob gx gy y) /\
    k == dh y gx)
  )
let initiator_authentication tr i alice bob gx gy k = ()

val responder_authentication: 
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
    (exists bob_si. is_corrupt tr (principal_state_label bob bob_si)) \/
    event_triggered (prefix tr i) alice (Initiate2 alice bob gx gy k)
  )
let responder_authentication tr i alice bob gx gy k = ()

(*** Forward Secrecy Properties ***)

/// This lemma is needed to proof the forward secrecy
/// security properties.
/// It is never explicitly called but automatically
/// instantiated via the SMTPat.
/// In the forward secrecy security property the problem
/// is that we do not explicitly have the session id
/// available. That is the reason for using the SMTPat.
///
/// Alternatively the SMTPat of the lemma 
/// principal_flow_to_principal_state in DY.Core.Label
/// could be extended with this SMTPat to proof the
/// forward secrecy security properties.
val principal_state_corrupt_implies_principal_corrupt:
  tr:trace -> prin:principal -> si:state_id -> 
  Lemma
  (requires
    trace_invariant tr /\
    is_corrupt tr (principal_state_label prin si)
  )
  (ensures
    is_corrupt tr (principal_label prin)
  )
  [SMTPat (trace_invariant tr); SMTPat (is_corrupt tr (principal_state_label prin si))]
let principal_state_corrupt_implies_principal_corrupt tr prin si = 
  // Triggers principal_flow_to_principal_state
  assert(principal_label prin `can_flow tr` principal_state_label prin si);
  // Triggers flow_to_public_eq
  assert(principal_label prin `can_flow tr` public);
  ()

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

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(is_publishable tr k);
  assert(is_corrupt tr (get_label k));

  assert(get_label k `can_flow tr` public);
  assert(is_corrupt tr (get_label k));
  assert(get_label k `can_flow tr` join (principal_state_label alice alice_si) (principal_label bob));
  assert(get_label k `can_flow tr` principal_state_label alice alice_si);
  assert(get_label k `can_flow tr` principal_label bob);

  assert(is_dh_shared_key tr alice bob k \/ is_corrupt tr (principal_label bob) \/
    is_corrupt tr (principal_state_label alice alice_si));
  assert(exists bob_si. get_label k `equivalent tr` 
    join (principal_state_label alice alice_si) (principal_state_label bob bob_si) \/ 
    is_corrupt tr (principal_label bob) \/
    is_corrupt tr (principal_state_label alice alice_si));

  // This assert is needed for the proof
  assert(exists bob_si. join (principal_state_label alice alice_si) (principal_state_label bob bob_si)
    `can_flow tr` public \/ 
    is_corrupt tr (principal_label bob));

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(principal_state_label alice alice_si `can_flow tr` public \/
    (exists bob_si. principal_state_label bob bob_si `can_flow tr` public) \/
    is_corrupt tr (principal_label bob));
  assert(exists bob_si. is_corrupt tr (join (principal_state_label alice alice_si) (principal_state_label bob bob_si)) \/ 
    is_corrupt tr (principal_label bob));
  
  assert(is_corrupt tr (principal_state_label alice alice_si) \/
    (exists bob_si. is_corrupt tr (principal_state_label bob bob_si)) \/
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob));
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

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(is_dh_shared_key tr alice bob k \/ is_corrupt tr (principal_label alice) \/
    is_corrupt tr (principal_state_label bob bob_si));

  assert(exists alice_si. get_label k `equivalent tr` 
    join (principal_state_label alice alice_si) (principal_state_label bob bob_si) \/ 
    is_corrupt tr (principal_label alice) \/
    is_corrupt tr (principal_state_label bob bob_si));
  
  // This assert is needed for the proof
  assert(exists alice_si. join (principal_state_label alice alice_si) (principal_state_label bob bob_si)
    `can_flow tr` public \/ 
    is_corrupt tr (principal_label alice));

  // The following code is not needed for the proof.
  // It just shows what we need to show to prove the lemma.
  assert(principal_state_label bob bob_si `can_flow tr` public \/
    (exists alice_si. principal_state_label alice alice_si `can_flow tr` public) \/
    is_corrupt tr (principal_label alice));
  assert(exists alice_si. is_corrupt tr (join (principal_state_label alice alice_si) (principal_state_label bob bob_si)) \/ 
    is_corrupt tr (principal_label alice));

  assert(is_corrupt tr (principal_state_label bob bob_si) \/
    (exists alice_si. is_corrupt tr (principal_state_label alice alice_si)) \/
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob));
  ()
