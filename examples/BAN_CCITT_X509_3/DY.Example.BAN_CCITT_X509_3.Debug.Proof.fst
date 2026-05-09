module DY.Example.BAN_CCITT_X509_3.Debug.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Lib.Comparse.Parsers
open DY.Example.BAN_CCITT_X509_3.Protocol.Total
open DY.Example.BAN_CCITT_X509_3.Protocol.Total.Proof
open DY.Example.BAN_CCITT_X509_3.Protocol.Stateful
open DY.Example.BAN_CCITT_X509_3.Protocol.Stateful.Proof
open DY.Example.BAN_CCITT_X509_3.Debug

#set-options "--fuel 1 --ifuel 1 --z3rlimit 1000 --split_queries always --z3cliopt 'smt.qi.eager_threshold=100'"

val debug_proof:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_private_keys_invariant
  )
  (ensures (let (_, tr_out) = debug () tr in trace_invariant tr_out))
let debug_proof tr =
  let alice = "alice" in
  let bob = "bob" in

  let (alice_priv_sid, tr) = initialize_private_keys alice tr in
  let (_, tr) = generate_private_key alice alice_priv_sid (LongTermSigKey "BAN_CCITT.SigKey") tr in
  let (_, tr) = generate_private_key alice alice_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey") tr in
  let (alice_pki_sid, tr) = initialize_pki alice tr in

  let (bob_priv_sid, tr) = initialize_private_keys bob tr in
  let (_, tr) = generate_private_key bob bob_priv_sid (LongTermSigKey "BAN_CCITT.SigKey") tr in
  let (_, tr) = generate_private_key bob bob_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey") tr in
  let (bob_pki_sid, tr) = initialize_pki bob tr in

  match compute_public_key bob bob_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey") tr with
  | (None, _) -> ()
  | (Some pk_b, tr) -> (
    match compute_public_key bob bob_priv_sid (LongTermSigKey "BAN_CCITT.SigKey") tr with
    | (None, _) -> ()
    | (Some vk_b, tr) -> (
      let (_, tr) = install_public_key alice alice_pki_sid (LongTermPkeKey "BAN_CCITT.PkeKey") bob pk_b tr in
      let (_, tr) = install_public_key alice alice_pki_sid (LongTermSigKey "BAN_CCITT.SigKey") bob vk_b tr in
      match compute_public_key alice alice_priv_sid (LongTermPkeKey "BAN_CCITT.PkeKey") tr with
      | (None, _) -> ()
      | (Some pk_a, tr) -> (
        match compute_public_key alice alice_priv_sid (LongTermSigKey "BAN_CCITT.SigKey") tr with
        | (None, _) -> ()
        | (Some vk_a, tr) -> (
          let (_, tr) = install_public_key bob bob_pki_sid (LongTermPkeKey "BAN_CCITT.PkeKey") alice pk_a tr in
          let (_, tr) = install_public_key bob bob_pki_sid (LongTermSigKey "BAN_CCITT.SigKey") alice vk_a tr in
          let alice_globals = { pki = alice_pki_sid; private_keys = alice_priv_sid } in
          let bob_globals = { pki = bob_pki_sid; private_keys = bob_priv_sid } in
          let x_a = serialize principal "Xa" in
          let y_a = serialize principal "Ya" in
          let x_b = serialize principal "Xb" in
          let y_b = serialize principal "Yb" in
          serialize_wf_lemma principal (is_publishable tr) "Xa";
          serialize_wf_lemma principal (is_publishable tr) "Ya";
          serialize_wf_lemma principal (is_publishable tr) "Xb";
          serialize_wf_lemma principal (is_publishable tr) "Yb";
          send_msg1_proof alice_globals alice bob x_a y_a tr;
          match send_msg1 alice_globals alice bob x_a y_a tr with
          | (None, _) -> ()
          | (Some (alice_si, msg1_id), tr) -> (
            receive_msg1_send_msg2_proof bob_globals bob alice msg1_id x_b y_b tr;
            match receive_msg1_send_msg2 bob_globals bob alice msg1_id x_b y_b tr with
            | (None, _) -> ()
            | (Some (bob_si, msg2_id), tr) -> (
              match receive_msg2_send_msg3 alice_globals alice alice_si bob msg2_id tr with
              | (None, _) -> ()
              | (Some msg3_id, tr) -> (
                match receive_msg3 bob_globals bob bob_si alice msg3_id tr with
                | _ -> ()
              )
            )
          )
        )
      )
    )
  )
