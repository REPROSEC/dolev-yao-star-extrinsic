module DY.Example.DH.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total.Proof
open DY.Example.DH.Protocol.Stateful
open DY.Example.DH.Protocol.Stateful.Proof

#set-options "--fuel 8 --ifuel 8 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*
  TODO: In the intrinsic version we use method like corrupt_at
  and did_event_occur_before. Do we need these method here too?
*)

(*** Authentication Properties ***)

val initiator_authentication: tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires event_triggered_at tr i alice (Initiate2 alice bob gx gy k) /\ 
    trace_invariant tr)
  (ensures is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
    (exists y. event_triggered (prefix tr i) bob (Respond1 alice bob gx gy y) /\
    k == dh y gx)
  )
let initiator_authentication tr i alice bob gx gy k = ()

val responder_authentication: tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires event_triggered_at tr i bob (Respond2 alice bob gx gy k) /\
    trace_invariant tr)
  (ensures is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
    event_triggered (prefix tr i) alice (Initiate2 alice bob gx gy k))
let responder_authentication tr i alice bob gx gy k = ()

(*** Key Secrecy Property ***)

val key_secrecy: tr:trace -> k:bytes -> alice:principal -> bob:principal ->
  Lemma
  (requires 
    trace_invariant tr /\
    attacker_knows tr k 
  )
  (ensures
    forall si sj. get_label k `equivalent tr` join (principal_state_label alice si) (principal_state_label bob sj) ==> 
    (is_corrupt tr (principal_state_label alice si) \/ is_corrupt tr (principal_state_label bob sj))
  )
let key_secrecy tr k alice bob = 
  attacker_only_knows_publishable_values tr k;

  normalize_term_spec is_corrupt;
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join);
  ()

(*** Forward Secrecy Properties ***)

val initiator_forward_secrecy: 
  tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i alice (Initiate2 alice bob gx gy k) /\
    attacker_knows tr k
  )
  (ensures
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
    (exists si sj. get_label k `equivalent tr` join (principal_state_label alice si) (principal_state_label bob sj) /\
      (is_corrupt tr (principal_state_label alice si) \/ is_corrupt tr (principal_state_label bob sj))
    )
  )
let initiator_forward_secrecy tr i alice bob gx gy k =
  attacker_only_knows_publishable_values tr k;
  
  (* Debugging code
  assert(is_dh_shared_key tr alice bob k \/ is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob)); *)

  normalize_term_spec is_corrupt;
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join);
  ()

val responder_forward_secrecy: 
  tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i bob (Respond2 alice bob gx gy k) /\
    attacker_knows tr k
  )
  (ensures
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob) \/
    (exists si sj. get_label k `equivalent tr` join (principal_state_label alice si) (principal_state_label bob sj) /\
      (is_corrupt tr (principal_state_label alice si) \/ is_corrupt tr (principal_state_label bob sj))
    )
  )
let responder_forward_secrecy tr i alice bob gx gy k = 
  attacker_only_knows_publishable_values tr k;

  (* Debugging code
  assert(is_dh_shared_key tr alice bob k \/ 
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob));
  assert(event_triggered tr alice (Initiate2 alice bob gx gy k) \/ 
    is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob)); *)
 
  normalize_term_spec is_corrupt;
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join);
  ()
