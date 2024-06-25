module DY.Example.DH.Debug.Proof

open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Stateful
open DY.Example.DH.Protocol.Stateful.Proof
open DY.Example.DH.Debug

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"
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
#pop-options

/// Other ways to proof the debug function
/// but I think the SMTPat way is the nicest one
(*
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"
val debug_proof2:
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
let debug_proof2 tr =
  (*** Initialize protocol run ***)
  let alice = "alice" in
  let bob = "bob" in

  let (alice_global_session_priv_key_id, tr) = initialize_private_keys alice tr in
  let (_, tr) = generate_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  
  let (bob_global_session_priv_key_id, tr) = initialize_private_keys bob tr in
  let (_, tr) = generate_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  let (priv_key_bob, tr) = get_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  match priv_key_bob with
  | None -> ()
  | Some priv_key_bob -> (    
    let pub_key_bob = vk priv_key_bob in    
    let (alice_global_session_pub_key_id, tr) = initialize_pki alice tr in    
    let (_, tr) = install_public_key alice alice_global_session_pub_key_id (Verify "DH.SigningKey") bob pub_key_bob tr in

    let (priv_key_alice, tr) = get_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey") tr in
    assert(trace_invariant tr);
    match priv_key_alice with
    | None -> ()
    | Some priv_key_alice -> (
      let pub_key_alice = vk priv_key_alice in      
      let (bob_global_session_pub_key_id, tr) = initialize_pki bob tr in
      let (_, tr) = install_public_key bob bob_global_session_pub_key_id (Verify "DH.SigningKey") alice pub_key_alice tr in

      let alice_global_session_ids: dh_global_sess_ids = {pki=alice_global_session_pub_key_id; private_keys=alice_global_session_priv_key_id} in
      let bob_global_session_ids: dh_global_sess_ids = {pki=bob_global_session_pub_key_id; private_keys=bob_global_session_priv_key_id} in

      (*** Run the protocol ***)
      prepare_msg1_proof tr alice bob;
      let (alice_session_id, tr) = prepare_msg1 alice bob tr in
      assert(trace_invariant tr);
      
      send_msg1_proof tr alice alice_session_id;
      let (msg1_id, tr) = send_msg1 alice alice_session_id tr in
      assert(trace_invariant tr);
      
      match msg1_id with
      | None -> ()
      | Some msg1_id -> (
        prepare_msg2_proof tr alice bob msg1_id;
        let (bob_session_id, tr) = prepare_msg2 alice bob msg1_id tr in
        assert(trace_invariant tr);
        
        match bob_session_id with
        | None -> ()
        | Some bob_session_id -> (
          send_msg2_proof tr bob_global_session_ids bob bob_session_id;         
          let (msg2_id, tr) = send_msg2 bob_global_session_ids bob bob_session_id tr in
          assert(trace_invariant tr);
          
          match msg2_id with
          | None -> ()
          | Some msg2_id -> (
            prepare_msg3_proof tr alice_global_session_ids alice bob msg2_id alice_session_id;
            let (_, tr) = prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id tr in

            send_msg3_proof tr alice_global_session_ids alice bob alice_session_id;
            let (msg3_id, tr) = send_msg3 alice_global_session_ids alice bob alice_session_id tr in
            assert(trace_invariant tr);
            
            match msg3_id with
            | None -> ()
            | Some msg3_id -> (
              verify_msg3_proof tr bob_global_session_ids alice bob msg3_id bob_session_id;
              let (_, tr) = verify_msg3 bob_global_session_ids alice bob msg3_id bob_session_id tr in
              assert(trace_invariant tr);
              ()
            )
          )        
        )
      )
    )
  )
#pop-options


#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
val prepare_msg1_proof_forall:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    forall alice bob.
      let (_, tr_out) = prepare_msg1 alice bob tr in
      trace_invariant tr_out
    )
  )
let prepare_msg1_proof_forall tr =
  introduce forall alice bob. trace_invariant (snd (prepare_msg1 alice bob tr))
  with (
    prepare_msg1_proof tr alice bob;
    let (alice_session_id, tr) = prepare_msg1 alice bob tr in
    ()
  )

val send_msg1_proof_forall:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    forall alice alice_session_id.
      let (_, tr_out) = send_msg1 alice alice_session_id tr in
      trace_invariant tr_out
    )
  )
let send_msg1_proof_forall tr =
  introduce forall alice alice_session_id. trace_invariant (snd (send_msg1 alice alice_session_id tr))
  with (
    send_msg1_proof tr alice alice_session_id;
    let (msg1_id, tr) = send_msg1 alice alice_session_id tr in
    ()
  )

val prepare_msg2_proof_forall:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    forall alice bob msg1_id.
      let (_, tr_out) = prepare_msg2 alice bob msg1_id tr in
      trace_invariant tr_out
    )
  )
let prepare_msg2_proof_forall tr =
  introduce forall alice bob msg1_id. trace_invariant (snd (prepare_msg2 alice bob msg1_id tr))
  with (
    prepare_msg2_proof tr alice bob msg1_id;
    let (bob_session_id, tr) = prepare_msg2 alice bob msg1_id tr in
    ()
  )

val send_msg2_proof_forall:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    forall bob_global_session_ids bob bob_session_id.
      let (_, tr_out) = send_msg2 bob_global_session_ids bob bob_session_id tr in
      trace_invariant tr_out
    )
  )
let send_msg2_proof_forall tr =
  introduce forall bob_global_session_ids bob bob_session_id. trace_invariant (snd (send_msg2 bob_global_session_ids bob bob_session_id tr))
  with (
    send_msg2_proof tr bob_global_session_ids bob bob_session_id;
    let (msg2_id, tr) = send_msg2 bob_global_session_ids bob bob_session_id tr in
    ()
  )

val prepare_msg3_proof_forall:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    forall alice_global_session_ids alice bob msg2_id alice_session_id.
      let (_, tr_out) = prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id tr in
      trace_invariant tr_out
    )
  )
let prepare_msg3_proof_forall tr =
  introduce forall alice_global_session_ids alice bob msg2_id alice_session_id. trace_invariant (snd (prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id tr))
  with (
    prepare_msg3_proof tr alice_global_session_ids alice bob msg2_id alice_session_id;
    let (_, tr) = prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id tr in
    ()
  )

val send_msg3_proof_forall:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    forall alice_global_session_ids alice bob alice_session_id.
      let (_, tr_out) = send_msg3 alice_global_session_ids alice bob alice_session_id tr in
      trace_invariant tr_out
    )
  )
let send_msg3_proof_forall tr =
  introduce forall alice_global_session_ids alice bob alice_session_id. trace_invariant (snd (send_msg3 alice_global_session_ids alice bob alice_session_id tr))
  with (
    send_msg3_proof tr alice_global_session_ids alice bob alice_session_id;
    let (msg3_id, tr) = send_msg3 alice_global_session_ids alice bob alice_session_id tr in
    ()
  )

val verify_msg3_proof_forall:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    forall bob_global_session_ids alice bob msg3_id bob_session_id.
      let (_, tr_out) = verify_msg3 bob_global_session_ids alice bob msg3_id bob_session_id tr in
      trace_invariant tr_out
    )
  )
let verify_msg3_proof_forall tr =
  introduce forall bob_global_session_ids alice bob msg3_id bob_session_id. trace_invariant (snd (verify_msg3 bob_global_session_ids alice bob msg3_id bob_session_id tr))
  with (
    verify_msg3_proof tr bob_global_session_ids alice bob msg3_id bob_session_id;
    let (_, tr) = verify_msg3 bob_global_session_ids alice bob msg3_id bob_session_id tr in
    ()
  )
#pop-options

#push-options "--fuel 8 --ifuel 8 --z3rlimit 50 --z3cliopt 'smt.qi.eager_threshold=100'"
val debug_proof_test:
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
let debug_proof_test tr =
  (*** Initialize protocol run ***)
  let alice = "alice" in
  let bob = "bob" in

  let (alice_global_session_priv_key_id, tr) = initialize_private_keys alice tr in
  let (_, tr) = generate_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  
  let (bob_global_session_priv_key_id, tr) = initialize_private_keys bob tr in
  let (_, tr) = generate_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  let (priv_key_bob, tr) = get_private_key bob bob_global_session_priv_key_id (Sign "DH.SigningKey") tr in
  match priv_key_bob with
  | None -> ()
  | Some priv_key_bob -> (    
    let pub_key_bob = vk priv_key_bob in    
    let (alice_global_session_pub_key_id, tr) = initialize_pki alice tr in    
    let (_, tr) = install_public_key alice alice_global_session_pub_key_id (Verify "DH.SigningKey") bob pub_key_bob tr in

    let (priv_key_alice, tr) = get_private_key alice alice_global_session_priv_key_id (Sign "DH.SigningKey") tr in
    assert(trace_invariant tr);
    match priv_key_alice with
    | None -> ()
    | Some priv_key_alice -> (
      let pub_key_alice = vk priv_key_alice in      
      let (bob_global_session_pub_key_id, tr) = initialize_pki bob tr in
      let (_, tr) = install_public_key bob bob_global_session_pub_key_id (Verify "DH.SigningKey") alice pub_key_alice tr in

      let alice_global_session_ids: dh_global_sess_ids = {pki=alice_global_session_pub_key_id; private_keys=alice_global_session_priv_key_id} in
      let bob_global_session_ids: dh_global_sess_ids = {pki=bob_global_session_pub_key_id; private_keys=bob_global_session_priv_key_id} in

      (*** Run the protocol ***)
      prepare_msg1_proof tr alice bob;
      let (alice_session_id, tr) = prepare_msg1 alice bob tr in
      assert(trace_invariant tr);
      
      send_msg1_proof tr alice alice_session_id;
      let (msg1_id, tr) = send_msg1 alice alice_session_id tr in
      assert(trace_invariant tr);
      
      match msg1_id with
      | None -> ()
      | Some msg1_id -> (
        prepare_msg2_proof tr alice bob msg1_id;
        let (bob_session_id, tr) = prepare_msg2 alice bob msg1_id tr in
        assert(trace_invariant tr);
        
        match bob_session_id with
        | None -> ()
        | Some bob_session_id -> (
          send_msg2_proof tr bob_global_session_ids bob bob_session_id;         
          let (msg2_id, tr) = send_msg2 bob_global_session_ids bob bob_session_id tr in
          assert(trace_invariant tr);
          
          match msg2_id with
          | None -> ()
          | Some msg2_id -> (
            prepare_msg3_proof tr alice_global_session_ids alice bob msg2_id alice_session_id;
            let (_, tr) = prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id tr in

            send_msg3_proof_forall tr;
            // This line is needed for the proof
            let (msg3_id, tr) = send_msg3 alice_global_session_ids alice bob alice_session_id tr in
            assert(trace_invariant tr);
            
            verify_msg3_proof_forall tr;
            ()
          )
        )
      )
    )
  )
*)
