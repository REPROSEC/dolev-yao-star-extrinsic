module DY.Example.BAN_CCITT_X509_3.Debug

open Comparse
open DY.Core
open DY.Lib
open DY.Lib.Comparse.Parsers
open DY.Example.BAN_CCITT_X509_3.Protocol.Total
open DY.Example.BAN_CCITT_X509_3.Protocol.Stateful

val debug: unit -> traceful (option unit)
let debug () =
  let alice = "alice" in
  let bob = "bob" in

  // Alice setup
  let* alice_priv_sid = initialize_private_keys alice in
  generate_private_key alice alice_priv_sid (LongTermSigKey "BAN_CCITT.SigKey");*
  generate_private_key alice alice_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey");*
  let* alice_pki_sid = initialize_pki alice in

  // Bob setup
  let* bob_priv_sid = initialize_private_keys bob in
  generate_private_key bob bob_priv_sid (LongTermSigKey "BAN_CCITT.SigKey");*
  generate_private_key bob bob_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey");*
  let* bob_pki_sid = initialize_pki bob in

  // Alice's PKI: Bob's keys
  let*? pk_b = compute_public_key bob bob_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey") in
  let*? vk_b = compute_public_key bob bob_priv_sid (LongTermSigKey "BAN_CCITT.SigKey") in
  install_public_key alice alice_pki_sid (LongTermPkeKey "BAN_CCITT.PkeKey") bob pk_b;*
  install_public_key alice alice_pki_sid (LongTermSigKey "BAN_CCITT.SigKey") bob vk_b;*

  // Bob's PKI: Alice's keys
  let*? pk_a = compute_public_key alice alice_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey") in
  let*? vk_a = compute_public_key alice alice_priv_sid (LongTermSigKey "BAN_CCITT.SigKey") in
  install_public_key bob bob_pki_sid (LongTermPkeKey "BAN_CCITT.PkeKey") alice pk_a;*
  install_public_key bob bob_pki_sid (LongTermSigKey "BAN_CCITT.SigKey") alice vk_a;*

  let alice_globals = { pki = alice_pki_sid; private_keys = alice_priv_sid } in
  let bob_globals = { pki = bob_pki_sid; private_keys = bob_priv_sid } in

  let x_a = serialize principal "Xa" in
  let y_a = serialize principal "Ya" in
  let x_b = serialize principal "Xb" in
  let y_b = serialize principal "Yb" in

  // Step 1
  let*? (alice_si, msg1_id) = send_msg1 alice_globals alice bob x_a y_a in
  
  // Step 2
  let*? (bob_si, msg2_id) = receive_msg1_send_msg2 bob_globals bob alice msg1_id x_b y_b in
  
  // Step 3
  let*? msg3_id = receive_msg2_send_msg3 alice_globals alice alice_si bob msg2_id in
  
  // Bob receives Step 3
  let*? _ = receive_msg3 bob_globals bob bob_si alice msg3_id in

  let* tr = get_trace in
  let _ = IO.debug_print_string (trace_to_string default_trace_to_string_printers tr) in
  return (Some ())

#push-options "--warn_error -272"
let _ = debug () empty_trace
#pop-options
