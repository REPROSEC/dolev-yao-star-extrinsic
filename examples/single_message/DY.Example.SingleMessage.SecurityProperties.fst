module DY.Example.SingleMessage.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleMessage.Protocol.Total.Proof
open DY.Example.SingleMessage.Protocol.Stateful
open DY.Example.SingleMessage.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10  --z3cliopt 'smt.qi.eager_threshold=100'"

val secret_secrecy_sender:
  tr:trace -> sender:principal -> receiver:principal -> secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr secret /\
    (exists sess_id. state_was_set tr sender sess_id (ClientState receiver secret))
  )
  (ensures
    is_corrupt tr (principal_label sender) \/ is_corrupt tr (principal_label receiver)
  )
let secret_secrecy_sender tr sender receiver secret =
  attacker_only_knows_publishable_values tr secret;
  ()
