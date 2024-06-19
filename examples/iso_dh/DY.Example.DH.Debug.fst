module DY.Example.DH.Debug

open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Stateful


let debug () : traceful (option unit)  =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  (*** Initialize protocol run ***)
  let alice = "alice" in
  let bob = "bob" in

  // Generate private key for Alice
  let* alice_global_session_priv_key_id = initialize_private_keys alice in
  generate_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey");*
  
  // Generate private key for Bob
  let* bob_global_session_priv_key_id = initialize_private_keys bob in
  generate_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey");*

  // Store Bob's public key in Alice's state
  // 1. Retrieve Bob's private key from his session
  // 2. Compute the public key from the private key
  // 3. Initialize Alice's session to store public keys
  // 4. Install Bob's public key in Alice's public key store
  let*? priv_key_bob = get_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey") in
  let pub_key_bob = vk priv_key_bob in
  let* alice_global_session_pub_key_id = initialize_pki alice in
  install_public_key alice alice_global_session_pub_key_id (Verify "DH.SigningKey") bob pub_key_bob;*

  // Store Alice's public key in Bob's state
  let*? priv_key_alice = get_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey") in
  let pub_key_alice = vk priv_key_alice in
  let* bob_global_session_pub_key_id = initialize_pki bob in
  install_public_key bob bob_global_session_pub_key_id (Verify "DH.SigningKey") alice pub_key_alice;*

  let alice_global_session_ids: dh_global_sess_ids = {pki=alice_global_session_pub_key_id; private_keys=alice_global_session_priv_key_id} in
  let bob_global_session_ids: dh_global_sess_ids = {pki=bob_global_session_pub_key_id; private_keys=bob_global_session_priv_key_id} in

  (*** Run the protocol ***)
  // Alice
  let* alice_session_id = prepare_msg1 alice bob in
  let*? msg1_id = send_msg1 alice alice_session_id in

  // Bob
  let*? bob_session_id = prepare_msg2 alice bob msg1_id in
  let*? msg2_id = send_msg2 bob_global_session_ids bob bob_session_id in

  // Alice
  prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id;*
  let*? msg3_id = send_msg3 alice_global_session_ids alice bob alice_session_id in

  // Bob
  verify_msg3 bob_global_session_ids alice bob msg3_id bob_session_id;*

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string default_trace_to_string_printers tr
    ) in

  return (Some ())

//Run ``debug ()`` when the module loads
#push-options "--warn_error -272"
let _ = debug () Nil
#pop-options