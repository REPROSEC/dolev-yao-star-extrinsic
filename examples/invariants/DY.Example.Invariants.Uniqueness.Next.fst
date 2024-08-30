module DY.Example.Invariants.Uniqueness.Next

open Comparse
open DY.Core
module L = DY.Core.Label
module Lib = DY.Lib
module List = FStar.List.Tot.Base
module Trace = DY.Core.Trace.Type

open DY.Example.Invariants.Uniqueness

#set-options "--fuel 1 --ifuel 1"

(*** Showing that the [next] protocol step maintains the trace invariant ***)

/// The main Lemma,
/// saying that the full state predicate is maintained,
/// when we add a new state to a session with the same idns
///
/// The proof looks at every other session (with sid_i <> sid) in the current full state.
/// The last SetState entry for sid_i comes
/// either
///   a) after 
/// or
///   b) before
/// the last SetState entry for sid.
/// We get that the idns in session sid_i are different from the ones in session sid
/// by looking at the full state pred at the last SetState entry for
///   a) sid_i
/// or
///   b) sid.

#push-options "--fuel 2 --z3rlimit 20 --z3cliopt 'smt.qi.eager_threshold=20'"
val state_same_idn_full_state_pred:
  tr:trace -> p:principal -> sid:state_id 
  -> new_cont:state_raw
  -> Lemma
    (requires (
         trace_invariant tr
       /\ has_state_for tr p sid
       /\ (let old_cont = access_state tr p sid in           
            Some? (parse p_state old_cont )
          /\ Some? (parse p_state new_cont )
          /\ (let Some old_st = parse p_state old_cont in
             let Some new_st = parse p_state new_cont in
               old_st.idn1 = new_st.idn1
             /\ old_st.idn2 = new_st.idn2
            )
         )
    ))
    (ensures
       full_state_pred tr (access_full_state tr p) p sid new_cont
    )
let state_same_idn_full_state_pred tr p sid new_cont =
  let old_cont = access_state tr p sid in
  let old_entry = (SetState p sid old_cont) in
  let Some (S the_idn1 the_idn2 the_ctr) = parse p_state new_cont in

  full_state_pred_forall_session_intro (access_full_state tr p) sid
  (fun sid_i sess_i ->
    let Snoc _ last_i = sess_i in
         match parse p_state last_i with
         | None -> False
         | Some last_i -> last_i.idn1 <> the_idn1 /\ last_i.idn2 <> the_idn2
  )
  (fun sid_i sess_i ->
     let Snoc _ last_i_b = sess_i in
     full_state_mem_get_session_get_state_forall p tr;
     match parse p_state last_i_b with
     | None -> session_parse_all tr p sid_i last_i_b
     | Some last_i -> (
         let tr_after_old = tr `suffix_after_event` old_entry in
         let last_i_entry = SetState p sid_i last_i_b in
         let tr_after_last_i = tr `suffix_after_event` last_i_entry in
         if tr_after_old `has_suffix` tr_after_last_i
           then ( // last_i after oldst on tr
             //admit();
             assert(no_set_state_entry_for p sid tr_after_last_i);
             let tr_before_last_i = tr `prefix_before_event` last_i_entry in
             suff_after_before_event_is_suff_at_event tr last_i_entry;
             no_set_state_entry_for_concat p sid (Snoc Nil last_i_entry) tr_after_last_i;
             get_state_same p sid tr_before_last_i tr;
             assert(old_cont = access_state tr_before_last_i p sid);
             assert(global_state_pred tr_before_last_i p sid_i last_i_b);
             get_state_appears_in_full_state tr_before_last_i p sid
           )
           else ( // oldst after last_i on tr
             //admit();
             suffixes tr tr_after_last_i tr_after_old;
             assert(tr_after_last_i `has_suffix` tr_after_old);

             get_state_no_set_state_for_on_suffix_after_event tr p sid_i;
             no_set_state_entry_for_on_suffix tr_after_last_i tr_after_old p sid_i;
             let tr_before_old = tr `prefix_before_event` old_entry in                               
             suff_after_before_event_is_suff_at_event tr old_entry;
             no_set_state_entry_for_concat p sid_i (Snoc Nil old_entry) tr_after_old;
             get_state_same p sid_i tr_before_old tr;
             let state_i_before_old = access_state tr_before_old p sid_i in
             assert(state_i_before_old = last_i_b);
             assert(global_state_pred tr_before_old p sid old_cont);
             get_state_appears_in_full_state tr_before_old p sid_i  
           )
     )
  )
#pop-options


/// Applying the above lemma to show that [next] maintains the trace invariant
#push-options "--z3rlimit 50 --z3cliopt 'smt.qi.eager_threshold=50'"
val next_invariant: tr:trace -> p:principal -> sid:state_id ->
  Lemma 
    (requires trace_invariant tr)
    (ensures  (
      let (_,tr_out) = next p sid tr in
      trace_invariant tr_out
      )
    )
let next_invariant tr p sid = 
  match get_state p sid tr with
  | (None, _) -> ()
  | (Some oldst_b, _) -> (
      match parse p_state oldst_b with
      | None -> ()
      | Some (S idn1 idn2 c) -> (          
          let msg = M p in
          let msg_b = serialize message msg in
          let (_, tr_after_msg) = send_msg msg_b tr in
          serialize_wf_lemma message (is_publishable tr) msg;

          let (_, tr_after_rand) = mk_rand NoUsage public 7 tr_after_msg in

          let next_state = S idn1 idn2 (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_rand in

          serialize_wf_lemma p_state (is_knowable_by (principal_state_label p sid) tr_after_rand) next_state;

          get_state_same p sid tr tr_after_msg;
          get_state_same p sid tr_after_msg tr_after_rand;

          state_same_idn_full_state_pred tr_after_rand p sid (serialize p_state (S idn1 idn2 (c+1)));

          let ev = E p in
          let ev_b = serialize p_event ev in
          let (_, tr_after_event) = trigger_event p "P" ev_b tr_after_next_state in

          let other_sid = {the_id = sid.the_id + 1} in
          match get_state p other_sid tr_after_event with
          | (None, _ ) -> ()
          | (Some ost_b, _) -> (
               match parse p_state ost_b with
               | None -> ()
               | Some (S other_idn1 other_idn2 other_c) ->
                   let other_state = S other_idn1 other_idn2 (other_c + 1) in
                   let other_state_b = serialize p_state other_state in
                   let (_, tr_after_other_session) = set_state p other_sid other_state_b tr_after_event in

                   parse_wf_lemma #bytes p_state #_ (is_knowable_by (principal_state_label p other_sid) tr_after_event) ost_b;
                   serialize_wf_lemma p_state (is_knowable_by (principal_state_label p other_sid) tr_after_event) other_state;

                   state_same_idn_full_state_pred tr_after_event p other_sid other_state_b
            )
        )
    )
#pop-options
