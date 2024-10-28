module DY.Example.DH.Debug.Proof

open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Stateful
open DY.Example.DH.Protocol.Stateful.Proof
open DY.Example.DH.Debug

/// This module proves that the debug function
/// fulfills the trace invariants.
///
/// The proof works automatically because each
/// stateful proof as a SMTPat (`[SMTPat (trace_invariant tr); SMTPat (protocol_function)]`).
/// Another way to do this proof is to basically
/// duplicate the code from the debug function and
/// call all the lemmas for the stateful code manually.

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20 --z3cliopt 'smt.qi.eager_threshold=100'"
val debug_proof:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = debug () tr in
    trace_invariant tr_out
    )
  )
let debug_proof tr = ()
