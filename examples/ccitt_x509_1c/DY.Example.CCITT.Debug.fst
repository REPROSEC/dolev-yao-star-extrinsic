module DY.Example.CCITT.Debug

open Comparse
open DY.Core
open DY.Lib
open DY.Example.CCITT.Protocol.Total
open DY.Example.CCITT.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(*** Example Protocol Run with Trace Printing ***)

let debug () : traceful (option unit)  =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  let alice = "alice" in
  let bob = "bob" in

  // Initialize state for Alice
  let* alice_priv_key_id = initialize_private_keys alice in
  generate_private_key alice alice_priv_key_id (LongTermSigKey ccitt_sign_tag);*
  let* alice_pki_id = initialize_pki alice in
  
  // Initialize state for Bob
  let* bob_priv_key_id = initialize_private_keys bob in
  generate_private_key bob bob_priv_key_id (LongTermPkeKey ccitt_pke_tag);*
  let* bob_pki_id = initialize_pki bob in

  // Install keys
  let*? vk_a = compute_public_key alice alice_priv_key_id (LongTermSigKey ccitt_sign_tag) in
  install_public_key bob bob_pki_id (LongTermSigKey ccitt_sign_tag) alice vk_a;*
  
  let*? pk_b = compute_public_key bob bob_priv_key_id (LongTermPkeKey ccitt_pke_tag) in
  install_public_key alice alice_pki_id (LongTermPkeKey ccitt_pke_tag) bob pk_b;*

  let alice_ids = {pki=alice_pki_id; private_keys=alice_priv_key_id} in
  let bob_ids = {pki=bob_pki_id; private_keys=bob_priv_key_id} in
  
  let ta = serialize string "2026-05-09" in
  let xa = serialize string "public data" in
  let ya = serialize string "secret data" in
  
  let*? msg1_id = alice_send_msg1 alice_ids.pki alice_ids.private_keys alice bob ta xa ya in
  let*? _ = bob_receive_msg1 bob_ids.pki bob_ids.private_keys bob alice msg1_id in
  
  let* tr = get_trace in
  let _ = IO.debug_print_string (trace_to_string default_trace_to_string_printers tr) in

  return (Some ())

#push-options "--warn_error -272"
let _ = debug () empty_trace
#pop-options
