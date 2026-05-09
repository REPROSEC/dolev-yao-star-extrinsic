module DY.Example.BAN_CCITT_X509_3.SecurityProperties

open DY.Core
open DY.Lib
open DY.Example.BAN_CCITT_X509_3.Protocol.Total
open DY.Example.BAN_CCITT_X509_3.Protocol.Total.Proof
open DY.Example.BAN_CCITT_X509_3.Protocol.Stateful
open DY.Example.BAN_CCITT_X509_3.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Authentication ***)

val authentication_a_to_b:
  tr:trace -> bob:principal -> alice:principal -> n_b:bytes ->
  Lemma
  (requires trace_invariant tr /\ event_triggered tr bob (Respond2 bob alice n_b))
  (ensures is_corrupt tr (long_term_key_label alice) \/ event_triggered tr alice (Initiate2 alice bob n_b))
let authentication_a_to_b tr bob alice n_b = ()

val authentication_b_to_a:
  tr:trace -> alice:principal -> bob:principal -> n_b:bytes ->
  Lemma
  (requires trace_invariant tr /\ event_triggered tr alice (Initiate2 alice bob n_b))
  (ensures is_corrupt tr (long_term_key_label bob) \/ (exists x_b y_b n_a. event_triggered tr bob (Respond1 bob alice n_b x_b y_b n_a)))
let authentication_b_to_a tr alice bob n_b = ()

(*** Confidentiality ***)

/// If Alice's payload y_a is labeled exactly with the shared secret label
/// (ban_ccitt_label alice bob) and is later publishable, then either alice
/// or bob's principal label has been corrupted.

val confidentiality_ya:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes -> x_a:bytes -> y_a:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    is_secret (ban_ccitt_label alice bob) tr y_a /\
    is_publishable tr y_a
  )
  (ensures
    is_corrupt tr (principal_label alice) \/
    is_corrupt tr (principal_label bob)
  )
let confidentiality_ya tr alice bob n_a x_a y_a = ()

val confidentiality_yb:
  tr:trace -> bob:principal -> alice:principal -> n_b:bytes -> x_b:bytes -> y_b:bytes -> n_a:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    is_secret (ban_ccitt_label alice bob) tr y_b /\
    is_publishable tr y_b
  )
  (ensures
    is_corrupt tr (principal_label alice) \/
    is_corrupt tr (principal_label bob)
  )
let confidentiality_yb tr bob alice n_b x_b y_b n_a = ()
