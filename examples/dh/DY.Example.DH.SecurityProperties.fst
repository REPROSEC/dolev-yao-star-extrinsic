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
val initiator_correspondence_lemma: tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires event_triggered_at tr i alice (Initiate2 alice bob gx gy k) /\ 
    trace_invariant tr)
  (ensures is_corrupt tr (principal_label bob) \/
    (exists y. event_triggered tr bob (Respond1 alice bob gx gy y) /\
    k == dh y gx)
  )
let initiator_correspondence_lemma tr i alice bob gx gy k = ()

val responder_correspondence_lemma: tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires event_triggered_at tr i bob (Respond2 alice bob gx gy k) /\
    trace_invariant tr)
  (ensures is_corrupt tr (principal_label alice) \/ 
    event_triggered tr alice (Initiate2 alice bob gx gy k))
let responder_correspondence_lemma tr i alice bob gx gy k = ()

val key_secrecy_lemma: tr:trace -> k:bytes -> alice:principal -> bob:principal ->
  Lemma
  (requires 
    trace_invariant tr /\
    attacker_knows tr k 
  )
  (ensures
    forall si sj. is_secret (join (principal_state_label alice si) (principal_state_label bob sj)) tr k ==> 
    (is_corrupt tr (principal_state_label alice si) \/ is_corrupt tr (principal_state_label bob sj))
  )
let key_secrecy_lemma tr k alice bob = attacker_only_knows_publishable_values tr k

val initiator_forward_secrecy_lemma: 
  tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i alice (Initiate2 alice bob gx gy k) /\
    attacker_knows tr k
  )
  (ensures
    is_corrupt tr (principal_label bob) \/
    (exists si sj. is_secret (join (principal_state_label alice si) (principal_state_label bob sj)) tr k /\
      (is_corrupt tr (principal_state_label alice si) \/ is_corrupt tr (principal_state_label bob sj))
    )
  )
let initiator_forward_secrecy_lemma tr i alice bob gx gy k = 
  attacker_only_knows_publishable_values tr k

val responder_forward_secrecy_lemma: 
  tr:trace -> i:nat -> alice:principal -> bob:principal -> gx:bytes -> gy:bytes -> k:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i bob (Respond2 alice bob gx gy k) /\
    attacker_knows tr k
  )
  (ensures
    is_corrupt tr (principal_label alice) \/
    (exists si sj. is_secret (join (principal_state_label alice si) (principal_state_label bob sj)) tr k /\
      (is_corrupt tr (principal_state_label alice si) \/ is_corrupt tr (principal_state_label bob sj))
    )
  )
let responder_forward_secrecy_lemma tr i alice bob gx gy k = 
  attacker_only_knows_publishable_values tr k
