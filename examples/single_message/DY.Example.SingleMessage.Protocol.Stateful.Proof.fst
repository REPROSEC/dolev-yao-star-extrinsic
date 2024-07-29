module DY.Example.SingleMessage.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleMessage.Protocol.Total
open DY.Example.SingleMessage.Protocol.Total.Proof
open DY.Example.SingleMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

let state_predicate_protocol: local_state_predicate login_state = {
  pred = (fun tr prin state_id st ->
    match st with
    | ClientState server secret -> (
      let client = prin in
      event_triggered tr client (ClientSendMsg client server secret) /\
      get_label secret == join (principal_label client) (principal_label server) /\
      is_knowable_by (join (principal_label client) (principal_label server)) tr secret
    )
    | ServerState secret -> (
      let server = prin in
      (exists client. event_triggered tr server (ServerReceivedMsg client server secret) /\
        is_knowable_by (join (principal_label client) (principal_label server)) tr secret
      ) //\/ is_publishable tr secret
    )
  );
  pred_later = (fun tr1 tr2 client state_id st -> ());
  pred_knowable = (fun tr client state_id st -> ());
}

let event_predicate_protocol: event_predicate login_event =
  fun tr prin e ->
    match e with
    | ClientSendMsg client server secret -> True
    | ServerReceivedMsg client server secret -> True (*
      event_triggered tr client (ClientSendMsg client server secret) \/ 
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
    *)

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (local_state_login_state.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_protocol);
]

/// List of all local event predicates.

let all_events = [
  (event_login_event.tag, compile_event_pred event_predicate_protocol)
]

/// Create the global trace invariants.

let trace_invariants_protocol: trace_invariants (crypto_invariants_protocol) = {
  state_pred = mk_state_pred crypto_invariants_protocol all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_protocol: protocol_invariants = {
  crypto_invs = crypto_invariants_protocol;
  trace_invs = trace_invariants_protocol;
}

/// Lemmas that the global state predicate contains all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate protocol_invariants_protocol) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  mk_state_pred_correct protocol_invariants_protocol all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate protocol_invariants_protocol) all_sessions)

val protocol_invariants_protocol_has_pki_invariant: squash (has_pki_invariant protocol_invariants_protocol)
let protocol_invariants_protocol_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_protocol_has_private_keys_invariant: squash (has_private_keys_invariant protocol_invariants_protocol)
let protocol_invariants_protocol_has_private_keys_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_protocol_has_nsl_session_invariant: squash (has_local_state_predicate protocol_invariants_protocol state_predicate_protocol)
let protocol_invariants_protocol_has_nsl_session_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct protocol_invariants_protocol all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events))

val protocol_invariants_protocol_has_nsl_event_invariant: squash (has_event_pred protocol_invariants_protocol event_predicate_protocol)
let protocol_invariants_protocol_has_nsl_event_invariant = all_events_has_all_events ()

(*** Proofs ***)

val prepare_message_proof:
  tr:trace -> client:principal -> server:principal ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = prepare_message client server tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (prepare_message client server tr)]
let prepare_message_proof tr client server = ()

val send_message_proof:
  tr:trace -> comm_keys_ids:communication_keys_sess_ids -> client:principal -> server:principal -> state_id:state_id ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = send_message comm_keys_ids client server state_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (send_message comm_keys_ids client server state_id tr)]
let send_message_proof tr comm_keys_ids client server state_id =
  match get_state client state_id tr with
  | (Some (ClientState server secret), tr) -> (
    compute_message_proof tr client server secret;
    assert(has_communication_layer_invariants crypto_invariants_protocol);
    send_confidential_proof #protocol_invariants_protocol tr comm_keys_ids client server (compute_message secret);
    ()
  )
  | _ -> ()

val receive_message_proof:
  tr:trace -> comm_keys_ids:communication_keys_sess_ids -> server:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = receive_message comm_keys_ids server msg_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (receive_message comm_keys_ids server msg_id tr)]
let receive_message_proof tr comm_keys_ids server msg_id =
  match receive_confidential comm_keys_ids server msg_id tr with
  | (Some {sender; receiver; payload}, tr) -> (
    match decode_message payload with
    | Some single_message -> (      
      match get_private_key server comm_keys_ids.private_keys (PkDec "DY.Lib.Communication.PublicKey") tr with
      | (None, tr) -> ()
      | (Some sk_receiver, tr) -> (
        match recv_msg msg_id tr with
        | (None, tr) -> ()
        | (Some msg_encrypted, tr) -> (
          let Some msg_plain = pk_dec sk_receiver msg_encrypted in 
          assert(has_communication_layer_invariants crypto_invariants_protocol);
          decrypt_message_proof #crypto_invariants_protocol tr server sk_receiver msg_encrypted;          
         
          assert(is_knowable_by (join (principal_label sender) (principal_label server)) tr payload);
          
          decode_message_proof tr sender server payload;
          
          assert(is_knowable_by (join (principal_label sender) (principal_label server)) tr single_message.secret);
          ()
        )
      )
    )
    | _ -> ()
  )
  | _ -> ()