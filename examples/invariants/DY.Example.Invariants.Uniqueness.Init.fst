module DY.Example.Invariants.Uniqueness.Init

open Comparse
open DY.Core
module L = DY.Lib
open DY.Example.Invariants.Uniqueness
open DY.Example.Invariants.Uniqueness.Identifier

#set-options "--fuel 1 --ifuel 1"

(*** Showing that the initial step maintains the trace invariant ***)

#push-options " --z3rlimit 30 --z3cliopt 'smt.qi.eager_threshold=20'"
val init_invariant: tr:trace -> p:principal ->
  Lemma 
    (requires trace_invariant tr)
    (ensures  (
      let (_,tr_out) = init p tr in
      trace_invariant tr_out
      )
    )
let init_invariant tr p =
  let (idn1, tr_after_new_idn1) = new_idn1 p tr in
  let (idn2, tr_after_new_idn2) = new_idn2 p tr in
  let new_state = S idn1 idn2 0 in
  let new_state_b = serialize p_state new_state in
  let (new_sess_id, _) = set_new_session p new_state_b tr_after_new_idn2 in
  
  serialize_wf_lemma p_state (is_knowable_by (principal_state_label p new_sess_id) tr_after_new_idn2) new_state;

  set_new_session_get_session p new_state_b tr_after_new_idn2;
  assert(tr = tr_after_new_idn2);
  match fst (get_full_state p tr_after_new_idn2) with
  | None -> ()
  | Some full_st ->
      full_state_pred_forall_session_intro full_st new_sess_id
        (fun sid_i sess_i ->
           let Snoc init_i last_i = sess_i in
           match parse p_state last_i with
           | None -> False
           | Some last_i ->
               last_i.idn1 <> idn1 /\ last_i.idn2 <> idn2
        )
        (fun sid_i sess_i ->
           let Snoc init_ last_i = sess_i in
           full_state_mem_get_session_get_state_forall p tr_after_new_idn2;
           match parse p_state last_i with
           | None -> session_parse_all tr p sid_i last_i
           | Some last_i -> 
               
              new_idn_does_not_appear_in_full_state_gen #p_state #nat #_ #_ #has_identifier__p_state_1 p tr;
               new_idn_does_not_appear_in_full_state #p_state #has_identifier_p_state_2 p tr
        )


    
