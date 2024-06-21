module DY.Example.DH.Debug.TraceInvariants

open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Stateful
open DY.Example.DH.Protocol.Stateful.Proof

/// This module provides a sanity check for the trace invariants.
/// It does this by showing that at least one trace satisfies the invariants.

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let debug (tr:trace) : string  =
  assume(trace_invariant tr);

  let _ = IO.debug_print_string "************* Trace *************\n" in
  (*** Initialize protocol run ***)
  let alice = "alice" in
  let bob = "bob" in

  // Generate private key for Alice
  let (alice_global_session_priv_key_id, tr) = initialize_private_keys alice tr in
  let (_, tr) = generate_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  
  // Generate private key for Bob
  let (bob_global_session_priv_key_id, tr) = initialize_private_keys bob tr in
  let (_, tr) = generate_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey") tr in

  // Store Bob's public key in Alice's state
  // 1. Retrieve Bob's private key from his session
  // 2. Compute the public key from the private key
  // 3. Initialize Alice's session to store public keys
  // 4. Install Bob's public key in Alice's public key store
  let (priv_key_bob, tr) = get_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  match priv_key_bob with
  | None -> "Failed to execute protocol run\n"
  | Some priv_key_bob -> (
    let pub_key_bob = vk priv_key_bob in
    let (alice_global_session_pub_key_id, tr) = initialize_pki alice tr in
    let (_, tr) = install_public_key alice alice_global_session_pub_key_id (Verify "DH.SigningKey") bob pub_key_bob tr in

    // Store Alice's public key in Bob's state
    let (priv_key_alice, tr) = get_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey") tr in
    match priv_key_alice with
    | None -> "Failed to execute protocol run\n"
    | Some priv_key_alice -> (
      let pub_key_alice = vk priv_key_alice in
      let (bob_global_session_pub_key_id, tr) = initialize_pki bob tr in
      let (_, tr) = install_public_key bob bob_global_session_pub_key_id (Verify "DH.SigningKey") alice pub_key_alice tr in

      let alice_global_session_ids: dh_global_sess_ids = {pki=alice_global_session_pub_key_id; private_keys=alice_global_session_priv_key_id} in
      let bob_global_session_ids: dh_global_sess_ids = {pki=bob_global_session_pub_key_id; private_keys=bob_global_session_priv_key_id} in

      (*** Run the protocol ***)
      // Alice
      prepare_msg1_proof tr alice bob;
      let (alice_session_id, tr) = prepare_msg1 alice bob tr in
      assert(trace_invariant tr);
      
      send_msg1_proof tr alice bob alice_session_id;
      let (msg1_id, tr) = send_msg1 alice alice_session_id tr in
      assert(trace_invariant tr);
      
      match msg1_id with
      | None -> "Failed to execute protocol run\n"
      | Some msg1_id -> (
        // Bob
        prepare_msg2_proof tr alice bob msg1_id;
        let (bob_session_id, tr) = prepare_msg2 alice bob msg1_id tr in
        assert(trace_invariant tr);
        
        match bob_session_id with
        | None -> "Failed to execute protocol run\n"
        | Some bob_session_id -> (
          send_msg2_proof tr bob_global_session_ids bob bob_session_id;         
          let (msg2_id, tr) = send_msg2 bob_global_session_ids bob bob_session_id tr in
          assert(trace_invariant tr);
          
          match msg2_id with
          | None -> "Failed to execute protocol run\n"
          | Some msg2_id -> (
            // Alice
            prepare_msg3_proof tr alice_global_session_ids alice bob msg2_id alice_session_id;
            let (_, tr) = prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id tr in
            assert(trace_invariant tr);
            
            send_msg3_proof tr alice_global_session_ids alice bob alice_session_id;
            let (msg3_id, tr) = send_msg3 alice_global_session_ids alice bob alice_session_id tr in
            assert(trace_invariant tr);
            
            match msg3_id with
            | None -> "Failed to execute protocol run\n"
            | Some msg3_id -> (
              // Bob
              verify_msg3_proof tr bob_global_session_ids alice bob msg3_id bob_session_id;
              let (_, tr) = verify_msg3 bob_global_session_ids alice bob msg3_id bob_session_id tr in
              assert(trace_invariant tr);

              trace_to_string default_trace_to_string_printers tr
            )
          )
        )
      )
    )
  )

//Run ``debug ()`` when the module loads
#push-options "--warn_error -272"
let tr_string = debug Nil
let _ = IO.debug_print_string (tr_string)
#pop-options