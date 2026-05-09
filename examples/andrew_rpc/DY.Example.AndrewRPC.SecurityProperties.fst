module DY.Example.AndrewRPC.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.AndrewRPC.Protocol.Total
open DY.Example.AndrewRPC.Protocol.Total.Proof
open DY.Example.AndrewRPC.Protocol.Stateful
open DY.Example.AndrewRPC.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50 --z3cliopt 'smt.qi.eager_threshold=100'"

val secrecy_of_k_prime_ab:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes -> k_prime_ab:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr bob (Respond1 alice bob n_a k_prime_ab) /\
    ~(is_corrupt tr (andrew_rpc_session_key_label alice bob n_a))
  )
  (ensures ~(attacker_knows tr k_prime_ab))
let secrecy_of_k_prime_ab tr alice bob n_a k_prime_ab =
  FStar.Classical.move_requires (attacker_only_knows_publishable_values tr) k_prime_ab

val authenticity_of_k_prime_ab:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes -> k_prime_ab:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr bob (Respond2 alice bob n_a k_prime_ab) /\
    ~(is_corrupt tr (andrew_rpc_session_key_label alice bob n_a))
  )
  (ensures event_triggered tr alice (Initiate2 alice bob n_a))
let authenticity_of_k_prime_ab tr alice bob n_a k_prime_ab =
  ()
