module DY.Test.Core.Trace.Modifies

open DY.Core

open FStar.Set

#set-options "--ifuel 0 --fuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This generally validates that the modifies analysis is working reasonably
/// automatically on simple programs, even if they make use of a variety of
/// trace-modifying features.
val broad_unmodified_test :
  principal -> traceful (option state_id)
let broad_unmodified_test prin =
  let* new_rand = mk_rand NoUsage (DY.Core.Label.principal_label prin) 32 in
  let* msg_ts = send_msg new_rand in
  trigger_event prin "test_event" (Literal (Seq.Base.empty));*
  let*? _ = recv_msg msg_ts in
  let* new_sid = new_session_id prin in
  let* _ = set_state prin new_sid new_rand in
  return (Some new_sid)

val broad_unmodified_proof :
  prin:principal -> sid:state_id ->
  content_opt:option bytes -> tr_in:trace ->
  Lemma (
    let (new_sid, tr_out) = broad_unmodified_test prin tr_in in
    (Some sid) == new_sid \/
    (is_most_recent_state_for prin sid content_opt tr_in ==>
     is_most_recent_state_for prin sid content_opt tr_out
    )
  )
let broad_unmodified_proof prin sid content_opt tr_in =
  let (new_sid, tr_out) = broad_unmodified_test prin tr_in in
  if Some sid = new_sid then ()
  else begin
    introduce is_most_recent_state_for prin sid content_opt tr_in ==>
              is_most_recent_state_for prin sid content_opt tr_out
    with _. traceful_is_most_recent_state_for_later prin sid content_opt (broad_unmodified_test prin) tr_in
  end

/// This test, similar to the previous, validates the modifies analysis, particularly
/// ensuring that the traceful option bind with *? works as well.
val optional_unmodified_test :
  principal -> traceful (option state_id)
let optional_unmodified_test prin =
  let* new_rand = mk_rand NoUsage (DY.Core.Label.principal_label prin) 32 in
  let* msg_ts = send_msg new_rand in
  trigger_event prin "test_event" (Literal (Seq.Base.empty));*
  let*? _ = recv_msg msg_ts in
  let* new_sid = new_session_id prin in
  let*? _ = get_state prin new_sid in
  return (Some new_sid)

val optional_unmodified_proof :
  prin:principal -> sid:state_id ->
  content_opt:option bytes -> tr_in:trace ->
  Lemma (
    let (new_sid_opt, tr_out) = optional_unmodified_test prin tr_in in
    (Some sid) == new_sid_opt \/
    (is_most_recent_state_for prin sid content_opt tr_in ==>
     is_most_recent_state_for prin sid content_opt tr_out
    )
  )
let optional_unmodified_proof prin sid content_opt tr_in =
  let (new_sid_opt, tr_out) = optional_unmodified_test prin tr_in in
  if (Some sid) = new_sid_opt then ()
  else begin
    introduce is_most_recent_state_for prin sid content_opt tr_in ==>
              is_most_recent_state_for prin sid content_opt tr_out
    with _. traceful_is_most_recent_state_for_later prin sid content_opt (optional_unmodified_test prin) tr_in
  end

/// The following tests ensure that the automation works despite branching, first
/// within a pure value, and then in the control flow.
assume val test_branch : bool

val branch_unmodified_test :
  principal -> traceful (option (state_id & state_id))
let branch_unmodified_test prin =
  let* new_rand = mk_rand NoUsage (DY.Core.Label.principal_label prin) 32 in
  let* msg_ts = send_msg new_rand in
  trigger_event prin "test_event" (Literal (Seq.Base.empty));*
  let*? _ = recv_msg msg_ts in
  let* new_sid1 = new_session_id prin in
  let* new_sid2 = new_session_id prin in
  let modify_sid = if test_branch then new_sid1 else new_sid2 in
  let* _ = set_state prin modify_sid new_rand in
  return (Some (new_sid1, new_sid2))

val branch_unmodified_proof :
  prin:principal -> sid:state_id ->
  content_opt:option bytes -> tr_in:trace ->
  Lemma
  (requires (
    let (sids_opt, _) = branch_unmodified_test prin tr_in in
    Some? sids_opt
  ))
  (ensures (
    let (Some (new_sid1, new_sid2), tr_out) = branch_unmodified_test prin tr_in in
    sid == new_sid1 \/
    sid == new_sid2 \/
    (is_most_recent_state_for prin sid content_opt tr_in ==>
     is_most_recent_state_for prin sid content_opt tr_out
    )
  ))
let branch_unmodified_proof prin sid content_opt tr_in =
  let (Some (new_sid1, new_sid2), tr_out) = branch_unmodified_test prin tr_in in
  if sid = new_sid1 || sid = new_sid2 then ()
  else begin
    introduce is_most_recent_state_for prin sid content_opt tr_in ==>
              is_most_recent_state_for prin sid content_opt tr_out
    with _. traceful_is_most_recent_state_for_later prin sid content_opt (branch_unmodified_test prin) tr_in
  end

val branch_unmodified_test_2 :
  principal -> traceful (option (state_id & state_id))
let branch_unmodified_test_2 prin =
  let* new_rand = mk_rand NoUsage (DY.Core.Label.principal_label prin) 32 in
  let* msg_ts = send_msg new_rand in
  trigger_event prin "test_event" (Literal (Seq.Base.empty));*
  let*? _ = recv_msg msg_ts in
  let* new_sid1 = new_session_id prin in
  let* new_sid2 = new_session_id prin in
  if test_branch
  then (
    let* _ = set_state prin new_sid1 new_rand in
    return (Some (new_sid1, new_sid2))
  )
  else
  return (Some (new_sid1, new_sid2))


val branch_unmodified_proof_2 :
  prin:principal -> sid:state_id ->
  content_opt:option bytes -> tr_in:trace ->
  Lemma
  (requires (
    let (sids_opt, _) = branch_unmodified_test_2 prin tr_in in
    Some? sids_opt
  ))
  (ensures (
    let (Some (new_sid1, new_sid2), tr_out) = branch_unmodified_test_2 prin tr_in in
    sid == new_sid1 \/
    (is_most_recent_state_for prin sid content_opt tr_in ==>
     is_most_recent_state_for prin sid content_opt tr_out
    )
  ))
let branch_unmodified_proof_2 prin sid content_opt tr_in =
  let (Some (new_sid1, new_sid2), tr_out) = branch_unmodified_test_2 prin tr_in in
  if sid = new_sid1 then ()
  else begin
    introduce is_most_recent_state_for prin sid content_opt tr_in ==>
              is_most_recent_state_for prin sid content_opt tr_out
    with _. traceful_is_most_recent_state_for_later prin sid content_opt (branch_unmodified_test_2 prin) tr_in
  end
