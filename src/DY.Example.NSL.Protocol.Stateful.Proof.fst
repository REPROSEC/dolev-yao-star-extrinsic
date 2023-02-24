module DY.Example.NSL.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total
open DY.Example.NSL.Protocol.Total.Proof
open DY.Example.NSL.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace predicates ***)

let nsl_session_pred: typed_session_pred nsl_session = {
  pred = (fun cpreds tr prin sess_id st ->
    match st with
    | InitiatorSentMsg1 bob n_a -> (
      let alice = prin in
      is_knowable_by cpreds (join (principal_label alice) (principal_label bob)) tr n_a /\
      event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate1 alice bob n_a))
    )
    | ResponderSentMsg2 alice n_a n_b -> (
      let bob = prin in
      is_knowable_by cpreds (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by cpreds (join (principal_label alice) (principal_label bob)) tr n_b /\
      event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 alice bob n_a n_b))
    )
    | InitiatorSentMsg3 bob n_a n_b  -> (
      let alice = prin in
      is_knowable_by cpreds (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by cpreds (join (principal_label alice) (principal_label bob)) tr n_b /\
      event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b))
    )
    | ResponderReceivedMsg3 alice n_a n_b -> (
      let bob = prin in
      is_knowable_by cpreds (join (principal_label alice) (principal_label bob)) tr n_a /\
      is_knowable_by cpreds (join (principal_label alice) (principal_label bob)) tr n_b /\
      event_triggered tr bob nsl_event_label (serialize nsl_event (Respond2 alice bob n_a n_b))
    )
  );
  pred_later = (fun cpreds tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun cpreds tr prin sess_id st -> ());
}

let all_sessions = [
  (pki_label, typed_session_pred_to_session_pred (map_session_invariant pki_pred));
  (private_keys_label, typed_session_pred_to_session_pred (map_session_invariant private_keys_pred));
  (nsl_session_label, typed_session_pred_to_session_pred nsl_session_pred);
]

val full_nsl_session_pred: state_predicate nsl_crypto_preds
let full_nsl_session_pred =
  mk_state_predicate nsl_crypto_preds all_sessions

let nsl_trace_preds: trace_predicates (nsl_crypto_preds) = {
  state_pred = full_nsl_session_pred;
  event_pred = (fun tr prin evt_label evt ->
    evt_label == nsl_event_label /\ (
      match parse nsl_event evt with
      | Some (Initiate1 alice bob n_a) -> (
        prin == alice /\
        get_label n_a == join (principal_label alice) (principal_label bob) /\
        0 < DY.Core.Trace.Type.length tr /\
        rand_generated_at tr (DY.Core.Trace.Type.length tr - 1) n_a
      )
      | Some (Respond1 alice bob n_a n_b) -> (
        prin == bob /\
        get_label n_b == join (principal_label alice) (principal_label bob) /\
        0 < DY.Core.Trace.Type.length tr /\
        rand_generated_at tr (DY.Core.Trace.Type.length tr - 1) n_b
      )
      | Some (Initiate2 alice bob n_a n_b) -> (
        prin == alice /\
        event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate1 alice bob n_a)) /\ (
          (join (principal_label alice) (principal_label bob)) `can_flow tr` public \/
          event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 alice bob n_a n_b))
        )
      )
      | Some (Respond2 alice bob n_a n_b) -> (
        prin == bob /\
        event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 alice bob n_a n_b)) /\ (
          (join (principal_label alice) (principal_label bob)) `can_flow tr` public \/
          event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b))
        )
      )
      | None -> False
    )
  );
}

let nsl_protocol_preds: protocol_predicates = {
  crypto_preds = nsl_crypto_preds;
  trace_preds = nsl_trace_preds;
}

inline_for_extraction noextract
val session_memP_tactic: unit -> FStar.Tactics.Tac unit
let session_memP_tactic () =
  FStar.Tactics.norm [delta_only [`%List.Tot.Base.memP; `%all_sessions]; iota; zeta]

val full_nsl_session_pred_has_pki_invariant: squash (has_pki_invariant nsl_protocol_preds)
let full_nsl_session_pred_has_pki_invariant =
  let lab = pki_label in
  let spred = typed_session_pred_to_session_pred (map_session_invariant pki_pred) in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  assert(List.Tot.memP (lab, spred) (all_sessions)) by (session_memP_tactic());
  mk_global_session_pred_correct nsl_protocol_preds (all_sessions) lab spred

val full_nsl_session_pred_has_private_keys_invariant: squash (has_private_keys_invariant nsl_protocol_preds)
let full_nsl_session_pred_has_private_keys_invariant =
  let lab = private_keys_label in
  let spred = typed_session_pred_to_session_pred (map_session_invariant private_keys_pred) in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  assert(List.Tot.memP (lab, spred) (all_sessions)) by (session_memP_tactic());
  mk_global_session_pred_correct nsl_protocol_preds (all_sessions) lab spred

val full_nsl_session_pred_has_nsl_invariant: squash (has_typed_session_pred nsl_protocol_preds nsl_session_label nsl_session_pred)
let full_nsl_session_pred_has_nsl_invariant =
  let lab = nsl_session_label in
  let spred = typed_session_pred_to_session_pred nsl_session_pred in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  assert(List.Tot.memP (lab, spred) (all_sessions)) by (session_memP_tactic());
  mk_global_session_pred_correct nsl_protocol_preds (all_sessions) lab spred

(*** Proof ***)

val prepare_msg1_proof:
  tr:trace ->
  alice:principal -> bob:principal ->
  Lemma
  (requires trace_invariant nsl_protocol_preds tr)
  (ensures (
    let (sess_id, tr_out) = prepare_msg1 alice bob tr in
    trace_invariant nsl_protocol_preds tr
  ))
let prepare_msg1_proof tr alice bob =
  ()

val send_msg1_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> sess_id:nat ->
  Lemma
  (requires trace_invariant nsl_protocol_preds tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg1 global_sess_id alice sess_id tr in
    match opt_msg_id with
    | None -> True
    | Some msg_id -> trace_invariant nsl_protocol_preds tr_out
  ))
let send_msg1_proof tr global_sess_id alice sess_id =
  let (opt_msg_id, tr_out) = send_msg1 global_sess_id alice sess_id tr in
  match opt_msg_id with
  | None -> ()
  | Some msg_id -> (
    let (Some st, tr) = get_typed_state #nsl_session nsl_session_label alice sess_id tr in
    let InitiatorSentMsg1 bob n_a = st in
    let (Some pk_b, tr) = get_public_key alice global_sess_id.pki PkEnc bob tr in
    let (nonce, tr) = mk_rand (principal_label alice) 32 tr in
    parse_serialize_inv_lemma #bytes nsl_event (Initiate1 alice bob n_a);
    compute_message1_proof tr alice bob pk_b n_a nonce
  )

val prepare_msg2_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> msg_id:nat ->
  Lemma
  (requires trace_invariant nsl_protocol_preds tr)
  (ensures (
    let (opt_sess_id, tr_out) = prepare_msg2 global_sess_id bob msg_id tr in
    match opt_sess_id with
    | None -> True
    | Some sess_id -> trace_invariant nsl_protocol_preds tr_out
  ))
let prepare_msg2_proof tr global_sess_id bob msg_id =
  let (opt_sess_id, tr_out) = prepare_msg2 global_sess_id bob msg_id tr in
  match opt_sess_id with
  | None -> ()
  | Some sess_id -> (
    let (Some msg, tr) = recv_msg msg_id tr in
    let (Some sk_b, tr) = get_private_key bob global_sess_id.private_keys PkDec tr in
    let (Some msg1, tr) = return (decode_message1 bob msg sk_b) tr in
    let msg1: message1 = msg1 in
    decode_message1_proof tr bob msg sk_b;
    let (n_b, tr) = mk_rand (join (principal_label msg1.alice) (principal_label bob)) 32 tr in
    parse_serialize_inv_lemma #bytes nsl_event (Respond1 msg1.alice bob msg1.n_a n_b)
  )

val send_msg2_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> sess_id:nat ->
  Lemma
  (requires trace_invariant nsl_protocol_preds tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg2 global_sess_id bob sess_id tr in
    match opt_msg_id with
    | None -> True
    | Some msg_id -> trace_invariant nsl_protocol_preds tr_out
  ))
let send_msg2_proof tr global_sess_id bob sess_id =
  let (opt_msg_id, tr_out) = send_msg2 global_sess_id bob sess_id tr in
  match opt_msg_id with
  | None -> ()
  | Some msg_id -> (
    let (Some st, tr) = get_typed_state nsl_session_label bob sess_id tr in
    let st: nsl_session = st in
    let ResponderSentMsg2 alice n_a n_b = st in
    let (Some pk_a, tr) = get_public_key bob global_sess_id.pki PkEnc alice tr in
    let (nonce, tr) = mk_rand (principal_label bob) 32 tr in
    let msg = compute_message2 bob {n_a; alice;} pk_a n_b nonce in
    parse_serialize_inv_lemma #bytes nsl_event (Respond1 alice bob n_a n_b);
    compute_message2_proof tr bob {n_a; alice;} pk_a n_b nonce
  )

val prepare_msg3_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> sess_id:nat -> msg_id:nat ->
  Lemma
  (requires trace_invariant nsl_protocol_preds tr)
  (ensures (
    let (opt_sess_id, tr_out) = prepare_msg3 global_sess_id alice sess_id msg_id tr in
    match opt_sess_id with
    | None -> True
    | Some sess_id -> trace_invariant nsl_protocol_preds tr_out
  ))
let prepare_msg3_proof tr global_sess_id alice sess_id msg_id =
  let (opt_sess_id, tr_out) = prepare_msg3 global_sess_id alice sess_id msg_id tr in
  match opt_sess_id with
  | None -> ()
  | Some _ -> (
    let (Some msg, tr) = recv_msg msg_id tr in
    let (Some sk_a, tr) = get_private_key alice global_sess_id.private_keys PkDec tr in
    let (Some st, tr) = get_typed_state nsl_session_label alice sess_id tr in
    let st: nsl_session = st in
    let InitiatorSentMsg1 bob n_a = st in
    let (Some msg2, tr) = return (decode_message2 alice bob msg sk_a n_a) tr in
    let msg2: message2 = msg2 in
    parse_serialize_inv_lemma #bytes nsl_event (Initiate1 alice bob n_a);
    decode_message2_proof tr alice bob msg sk_a n_a;
    parse_serialize_inv_lemma #bytes nsl_event (Initiate2 alice bob n_a msg2.n_b)
  )

val send_msg3_proof:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> alice:principal -> sess_id:nat ->
  Lemma
  (requires trace_invariant nsl_protocol_preds tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg3 global_sess_id alice sess_id tr in
    match opt_msg_id with
    | None -> True
    | Some msg_id -> trace_invariant nsl_protocol_preds tr_out
  ))
let send_msg3_proof tr global_sess_id alice sess_id =
  let (opt_msg_id, tr_out) = send_msg3 global_sess_id alice sess_id tr in
  match opt_msg_id with
  | None -> ()
  | Some msg_id -> (
    let (Some st, tr) = get_typed_state nsl_session_label alice sess_id tr in
    let st: nsl_session = st in
    let InitiatorSentMsg3 bob n_a n_b = st in
    let (Some pk_b, tr) = get_public_key alice global_sess_id.pki PkEnc bob tr in
    let (nonce, tr) = mk_rand (principal_label alice) 32 tr in
    let msg = compute_message3 alice bob pk_b n_b nonce in
    compute_message3_proof tr alice bob pk_b n_b nonce
  )

val prepare_msg4:
  tr:trace ->
  global_sess_id:nsl_global_sess_ids -> bob:principal -> sess_id:nat -> msg_id:nat ->
  Lemma
  (requires trace_invariant nsl_protocol_preds tr)
  (ensures (
    let (opt_sess_id, tr_out) = prepare_msg4 global_sess_id bob sess_id msg_id tr in
    match opt_sess_id with
    | None -> True
    | Some sess_id -> trace_invariant nsl_protocol_preds tr_out
  ))
let prepare_msg4 tr global_sess_id bob sess_id msg_id =
  let (opt_sess_id, tr_out) = prepare_msg4 global_sess_id bob sess_id msg_id tr in
  match opt_sess_id with
  | None -> ()
  | Some _ -> (
    let (Some msg, tr) = recv_msg msg_id tr in
    let (Some sk_b, tr) = get_private_key bob global_sess_id.private_keys PkDec tr in
    let (Some st, tr) = get_typed_state nsl_session_label bob sess_id tr in
    let st: nsl_session = st in
    let ResponderSentMsg2 alice n_a n_b = st in
    let (Some msg3, tr) = return (decode_message3 alice bob msg sk_b n_b) tr in
    parse_serialize_inv_lemma #bytes nsl_event (Respond1 alice bob n_a n_b);
    decode_message3_proof tr alice bob msg sk_b n_b;
    // From the decode_message3 proof, we get the following fact:
    // exists n_a'. event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a' n_b))
    // We want to obtain the same fact, with the actual n_a (not the one from the exists, n_a')
    // We prove it like this:
    // We know from the state predicate that the event Respond1 alice bob n_a n_b was triggered
    // Moreover, Initiate2 alice bob n_a' n_b implies Respond1 alice bob n_a' n_b (modulo corruption)
    // From the event predicate, we know that n_b was generated just before each Respond1 event
    // Hence the two Respond1 events are equal, and we get n_a == n_a'
    let msg3: message3 = msg3 in
    introduce (~((join (principal_label alice) (principal_label bob)) `can_flow tr` public)) ==> event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a n_b)) with _. (
      eliminate exists n_a'. event_triggered tr alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a' n_b))
      returns _
      with _. (
        assert(exists tr_before. tr_before <$ tr /\ nsl_protocol_preds.trace_preds.event_pred tr_before alice nsl_event_label (serialize nsl_event (Initiate2 alice bob n_a' n_b)));
        parse_serialize_inv_lemma #bytes nsl_event (Initiate2 alice bob n_a' n_b);
        parse_serialize_inv_lemma #bytes nsl_event (Initiate2 alice bob n_a n_b);
        parse_serialize_inv_lemma #bytes nsl_event (Respond1 alice bob n_a n_b);
        parse_serialize_inv_lemma #bytes nsl_event (Respond1 alice bob n_a' n_b);
        assert(event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 alice bob n_a n_b)) /\ event_triggered tr bob nsl_event_label (serialize nsl_event (Respond1 alice bob n_a' n_b)) ==> n_a == n_a')
      )
    );
    parse_serialize_inv_lemma #bytes nsl_event (Respond2 alice bob n_a n_b)
  )
