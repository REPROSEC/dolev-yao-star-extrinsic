module DY.Example.AndrewRPC.Debug.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.AndrewRPC.Protocol.Total
open DY.Example.AndrewRPC.Protocol.Total.Proof
open DY.Example.AndrewRPC.Protocol.Stateful
open DY.Example.AndrewRPC.Protocol.Stateful.Proof
open DY.Example.AndrewRPC.Debug

#set-options "--fuel 1 --ifuel 2 --z3rlimit 800 --z3cliopt 'smt.qi.eager_threshold=100'"

val debug_proof:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_private_keys_invariant
  )
  (ensures (
    let (_, tr_out) = debug () tr in
    trace_invariant tr_out
  ))
let debug_proof tr =
  let alice = "alice" in
  let bob = "bob" in
  let (_, tr1) = initialize_pki alice tr in
  let (_, tr2) = initialize_pki bob tr1 in
  let (_, tr3) = initialize_private_keys alice tr2 in
  let (_, tr4) = initialize_private_keys bob tr3 in
  let kab_usg = AeadKey andrew_rpc_kab_tag (serialize _ {akd_alice = alice; akd_bob = bob}) in
  let (kab, tr5) = mk_rand kab_usg (andrew_rpc_nonce_label alice bob) 32 tr4 in
  mk_rand_bytes_invariant kab_usg (andrew_rpc_nonce_label alice bob) 32 tr4;
  mk_rand_get_label kab_usg (andrew_rpc_nonce_label alice bob) 32 tr4;
  mk_rand_has_usage kab_usg (andrew_rpc_nonce_label alice bob) 32 tr4;
  assert(is_kab_for tr5 kab alice bob);
  alice_send_msg1_proof alice bob tr5;
  let ((alice_sid, msg1_id), tr6) = alice_send_msg1 alice bob tr5 in
  bob_recv_msg1_send_msg2_proof bob alice kab msg1_id tr6;
  match bob_recv_msg1_send_msg2 bob alice kab msg1_id tr6 with
  | (None, _) -> ()
  | (Some (bob_sid, msg2_id), tr7) -> (
    alice_recv_msg2_send_msg3_proof alice bob alice_sid kab msg2_id tr7;
    match alice_recv_msg2_send_msg3 alice bob alice_sid kab msg2_id tr7 with
    | (None, _) -> ()
    | (Some msg3_id, tr8) -> (
      bob_recv_msg3_send_msg4_proof bob bob_sid msg3_id tr8
    )
  )
