module DY.Example.AndrewRPC.Debug

open Comparse
open DY.Core
open DY.Lib
open DY.Example.AndrewRPC.Protocol.Total
open DY.Example.AndrewRPC.Protocol.Stateful

val debug: unit -> traceful (option unit)
let debug () =
  let alice = "alice" in
  let bob = "bob" in
  let* _ = initialize_pki alice in
  let* _ = initialize_pki bob in
  let* _ = initialize_private_keys alice in
  let* _ = initialize_private_keys bob in
  let* kab = mk_rand (AeadKey andrew_rpc_kab_tag (serialize _ {akd_alice = alice; akd_bob = bob})) (andrew_rpc_nonce_label alice bob) 32 in
  let* (alice_sid, msg1_id) = alice_send_msg1 alice bob in
  let*? (bob_sid, msg2_id) = bob_recv_msg1_send_msg2 bob alice kab msg1_id in
  let*? msg3_id = alice_recv_msg2_send_msg3 alice bob alice_sid kab msg2_id in
  let*? msg4_id = bob_recv_msg3_send_msg4 bob bob_sid msg3_id in
  let* tr = get_trace in
  let _ = IO.debug_print_string "Andrew RPC trace:\n" in
  let _ = IO.debug_print_string (trace_to_string default_trace_to_string_printers tr) in
  return (Some ())

#push-options "--warn_error -272"
let _ = debug () empty_trace
#pop-options
