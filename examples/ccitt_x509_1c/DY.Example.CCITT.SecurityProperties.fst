module DY.Example.CCITT.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.CCITT.Protocol.Total
open DY.Example.CCITT.Protocol.Total.Proof
open DY.Example.CCITT.Protocol.Stateful
open DY.Example.CCITT.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

/// Authentication: if Bob successfully received the protocol message and the
/// long-term keys are not corrupt, Alice indeed triggered the matching AliceSends.
val authentication_bob:
  tr:trace ->
  alice:principal -> bob:principal ->
  ta:bytes -> na:bytes -> xa:bytes -> ya:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr bob (BobReceives alice bob ta na xa ya) /\
    ~(is_corrupt tr (ccitt_label alice bob))
  )
  (ensures
    event_triggered tr alice (AliceSends alice bob ta na xa ya)
  )
let authentication_bob tr alice bob ta na xa ya = ()

/// Secrecy: if ya is a secret value labelled with ccitt_label alice bob
/// (i.e. only knowable to Alice and Bob), and that label is not corrupt,
/// then the attacker cannot learn ya.
val secrecy_ya:
  tr:trace ->
  alice:principal -> bob:principal -> ya:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    is_secret (ccitt_label alice bob) tr ya /\
    ~(is_corrupt tr (ccitt_label alice bob))
  )
  (ensures
    ~(attacker_knows tr ya)
  )
let secrecy_ya tr alice bob ya =
  FStar.Classical.move_requires (attacker_only_knows_publishable_values tr) ya
