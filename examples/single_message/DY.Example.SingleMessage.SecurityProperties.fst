module DY.Example.SingleMessage.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleMessage.Protocol.Total.Proof
open DY.Example.SingleMessage.Protocol.Stateful
open DY.Example.SingleMessage.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

val receiver_authentication:
  tr:trace -> i:timestamp ->
  sender:principal -> receiver:principal -> secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i sender (ClientSendMsg sender receiver secret)
  )
  (ensures
    is_corrupt tr (principal_label sender) \/ is_corrupt tr (principal_label receiver) \/
    (exists i'. event_triggered i' receiver (ServerReceivedMsg sender receiver secret))
  )
let receiver_authentication tr i sender receiver secret = admit()

val secret_secrecy:
  tr:trace -> sender:principal -> receiver:principal -> secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr secret /\
    ((exists sess_id. state_was_set tr sender sess_id (ClientState receiver secret)) \/
    (exists sess_id. state_was_set tr receiver sess_id (ServerState secret)))
  )
  (ensures
    is_corrupt tr (principal_label sender) \/ is_corrupt tr (principal_label receiver)
  )
let secret_secrecy tr sender receiver secret =
  attacker_only_knows_publishable_values tr secret;
  admit();
  ()