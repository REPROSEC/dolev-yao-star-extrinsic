module DY.Example.NSL.Debug

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total
open DY.Example.NSL.Protocol.Stateful
open DY.Example.NSL.Debug.Printing

(*** Example Protocol Run with Trace Printing ***)

let debug () : traceful (option unit)  =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  (*** Initialize protocol run ***)
  let alice = "alice" in
  let bob = "bob" in

  // Generate private key for Alice
  let* alice_global_session_priv_key_id = initialize_private_keys alice in
  generate_private_key alice alice_global_session_priv_key_id (LongTermPkeKey "NSL.PublicKey");*
  
  // Generate private key for Bob
  let* bob_global_session_priv_key_id = initialize_private_keys bob in
  generate_private_key bob bob_global_session_priv_key_id (LongTermPkeKey "NSL.PublicKey");*

  // Store Bob's public key in Alice's state
  // 1. Retrieve Bob's private key from his session
  // 2. Compute the public key from the private key
  // 3. Initialize Alice's session to store public keys
  // 4. Install Bob's public key in Alice's public key store
  let*? priv_key_bob = get_private_key bob bob_global_session_priv_key_id (LongTermPkeKey "NSL.PublicKey") in
  let*? pub_key_bob = compute_public_key bob bob_global_session_priv_key_id (LongTermPkeKey "NSL.PublicKey") in
  let* alice_global_session_pub_key_id = initialize_pki alice in
  install_public_key alice alice_global_session_pub_key_id (LongTermPkeKey "NSL.PublicKey") bob pub_key_bob;*

  // Store Alice's public key in Bob's state
  let*? priv_key_alice = get_private_key alice alice_global_session_priv_key_id (LongTermPkeKey "NSL.PublicKey") in
  let*? pub_key_alice = compute_public_key alice alice_global_session_priv_key_id (LongTermPkeKey "NSL.PublicKey") in
  let* bob_global_session_pub_key_id = initialize_pki bob in
  install_public_key bob bob_global_session_pub_key_id (LongTermPkeKey "NSL.PublicKey") alice pub_key_alice;*

  let alice_global_session_ids: nsl_global_sess_ids = {pki=alice_global_session_pub_key_id; private_keys=alice_global_session_priv_key_id} in
  let bob_global_session_ids: nsl_global_sess_ids = {pki=bob_global_session_pub_key_id; private_keys=bob_global_session_priv_key_id} in
  
  (*** Run the protocol ***)
  // Alice send message 1
  let* alice_session_id = prepare_msg1 alice bob in
  let*? msg1_id = send_msg1 alice_global_session_ids alice alice_session_id in

  // Bob receive message 1 and send message 2
  let*? bob_session_id = prepare_msg2 bob_global_session_ids bob msg1_id in
  let*? msg2_id = send_msg2 bob_global_session_ids bob bob_session_id in

  // Alice receive message 2 and send message 3
  prepare_msg3 alice_global_session_ids alice alice_session_id msg2_id;*
  let*? msg3_id = send_msg3 alice_global_session_ids alice alice_session_id in

  // Bob receive message 3
  prepare_msg4 bob_global_session_ids bob bob_session_id msg3_id;*

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string (get_nsl_trace_to_string_printers priv_key_alice priv_key_bob) tr
    ) in

  return (Some ())

//Run ``debug ()`` when the module loads
#push-options "--warn_error -272"
let _ = debug () Nil
#pop-options
