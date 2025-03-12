module DY.Test.Core.Trace.Modifies

open DY.Core

open FStar.Set

#set-options "--ifuel 0 --fuel 0"

let unmodified_test (prin:principal) (sid:state_id)
  : traceful (option bytes & option bytes)
  = let* st_opt1 = get_state prin sid in
    let* new_rand = mk_rand NoUsage (DY.Core.Label.principal_label prin) 32 in
    let* msg_ts = send_msg new_rand in
    trigger_event prin "test_event" (Literal (Seq.Base.empty));*
    let* _ = recv_msg msg_ts in
    let* st_opt2 = get_state prin sid in
    return (st_opt1, st_opt2)

let unmodified_test_proof (prin:principal) (sid:state_id) (tr_in:trace)
  : Lemma
    (let ((st_opt1, st_opt2), _) = unmodified_test prin sid tr_in in
     st_opt1 == st_opt2
    )
  = traceful_unmodified_same_state_aux prin sid (unmodified_test prin sid) tr_in;
    ()
