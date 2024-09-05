module DY.Example.Invariants.Uniqueness.Injectivity

open DY.Example.Invariants.Uniqueness

open Comparse
open DY.Core
module Lib = DY.Lib

module Trace = DY.Core.Trace.Type

#set-options "--fuel 1 --ifuel 1"

let rec sessions_history
  (tr:trace) (p:principal) (sid:state_id):
  Lemma
  (requires has_session_for tr p sid
  )
  (ensures (
    let Snoc init last = access_session tr p sid in

    match init with
    | Nil -> True
    | _ -> 
      let tr_before =(tr `prefix_before_event` (SetState p sid last)) in
    has_session_for tr_before p sid
    /\ init = access_session tr_before p sid
  ))
  (decreases (Trace.length tr))
  = 
  let Snoc init last = access_session tr p sid in
  match init with
  | Nil -> ()
  | _ -> (
    match tr with 
    | Nil -> ()
    | Snoc tr_init (SetState p' sid' cont') -> (
        if p' = p && sid' = sid
        then (
      let tr_before =(tr `prefix_before_event` (SetState p sid last)) in
      sessions_history tr_before p sid
   )
      else sessions_history tr_init p sid
  )
    | Snoc tr_init _ -> sessions_history tr_init p sid
    )

let rec session_mem_state_was_set
  (tr:trace) (p:principal) (sid:state_id) (sess:session_raw) (cont:state_raw):
  Lemma
  (requires (
     has_session_for tr p sid /\
     sess = access_session tr p sid /\
     cont `memP` sess
  ))
  (ensures (
     let Snoc _ last = access_session tr p sid in

     if cont = last
     then True
     else
     state_was_set (tr `prefix_before_event` (SetState p sid last)) p sid cont
  ))
  (decreases Trace.length tr)
  = 
     let Snoc init last = access_session tr p sid in
     if last = cont
     then ()
     else (
     memP_singleton  last cont;
     assert(Snoc? init);
        sessions_history tr p sid;
     session_mem_state_was_set (tr `prefix_before_event` (SetState p sid last)) p sid init cont
     )

#push-options "--z3rlimit 20"
let rec session_has_same_idn1 
  (tr:trace) (p:principal) (sid:state_id) (cont:state_raw):
  Lemma 
  (requires trace_invariant tr 
    /\ state_was_set tr p sid cont
    /\ (let sess = access_session tr p sid in
     cont `memP` sess
    
    /\ Some? (parse p_state cont)
    /\ ( let Snoc _ last = sess in
        Some? (parse p_state last)
    ))
  )
  (ensures (
     let sess = access_session tr p sid in
     let Snoc _ last_b = sess in
     let last = Some?.v (parse p_state last_b) in
     let st = Some?.v (parse p_state cont) in

     st.idn1 = last.idn1
     
  ))
  (decreases (Trace.length tr))
=    let sess = access_session tr p sid in
     let Snoc init last_b = sess in
     let last = Some?.v (parse p_state last_b) in
     let st = Some?.v (parse p_state cont) in
  if last_b = cont 
  then ()
  else (
    let tr_before_last = tr `prefix_before_event` (SetState p sid last_b) in
    normalize_term_spec trace_invariant;
    prefix_before_event_invariant tr (SetState p sid last_b);
    assert(trace_invariant tr_before_last);
    sessions_history tr p sid;
    assert(cont `memP` init);
    session_mem_state_was_set tr_before_last p sid init cont;
    // assert(state_was_set tr_before_last p sid cont);
    // assert(init = access_session tr_before_last p sid);
    session_has_same_idn1 tr_before_last p sid cont
  )
#pop-options 



#push-options "--z3rlimit 20 --z3cliopt 'smt.qi.eager_threshold=20'"
let state_injective_ (tr:trace)
  (p:principal)
  // (sid sid': state_id)
  // (cont:state_raw) (cont':state_raw{cont <> cont'}): 
  (ev_sid:trace_event) (ev_sid':trace_event):
  Lemma
  (requires
       trace_invariant tr
     /\ ev_sid `memP` tr /\ ev_sid' `memP` tr
     /\ ev_sid <> ev_sid'
     /\  SetState? ev_sid
     /\ SetState? ev_sid'
     /\ ( let SetState p_sid sid cont = ev_sid in
       let SetState p_sid' sid' cont' = ev_sid' in
       p_sid = p /\ p_sid' = p
       /\ (
     assert(state_was_set tr p sid cont);
     assert(state_was_set tr p sid' cont');
       let st = Some?.v (parse p_state cont) in  
        let st' = Some?.v (parse p_state cont') in  
        st.idn1 = st'.idn1
     ))
     /\ ev_sid `before_on tr` ev_sid'
   
     )
  (ensures
    (let SetState p sid cont = ev_sid in
     let SetState p sid' cont' = ev_sid' in
      sid = sid'
     )
  )
  = let SetState p sid cont = ev_sid in
    let SetState p sid' cont' = ev_sid' in
    assert(state_was_set tr p sid cont);
    assert(state_was_set tr p sid' cont');
  introduce ev_sid `before_on tr` ev_sid' ==> sid = sid'
  with _ .
  let st = Some?.v (parse p_state cont) in  
  let st' = Some?.v (parse p_state cont') in  
  
   introduce sid <> sid' ==> st.idn1 <> st'.idn1
   with _ . (
   let tr_before_cont' = tr `prefix_before_event` ev_sid' in
   normalize_term_spec trace_invariant;
     state_was_set_appears_in_full_state tr_before_cont' p sid cont;
     state_was_set_appears_in_session tr_before_cont' p sid cont;
     assert(global_state_pred tr_before_cont' p sid' cont');
     state_was_set_get_state p sid cont tr_before_cont';
     let Snoc _ last = access_session tr_before_cont' p sid in
     prefix_before_event_invariant tr ev_sid';
     assert(trace_invariant tr_before_cont');
     session_parse_all tr_before_cont' p sid last;
     session_has_same_idn1 tr_before_cont' p sid cont;
     full_state_some_get_session_get_state p sid tr_before_cont';
     ()
   )
#pop-options 

(** The arity 3 version of [move_requires] *)
val move_requires_4
      (#a #b #c #d: Type)
      (#p #q: (a -> b -> c -> d -> Type))
      ($_: (x: a -> y: b -> z: c -> zz:d -> Lemma (requires (p x y z zz)) (ensures (q x y z zz))))
      (x: a)
      (y: b)
      (z: c)
      (zz : d)
    : Lemma (p x y z zz ==> q x y z zz)
let move_requires_4 #a #b #c #d #p #q f x y z zz = FStar.Classical.move_requires (f x y z) zz

#push-options "--z3rlimit 20 --fuel 4  --z3cliopt 'smt.qi.eager_threshold=20'"
let state_injective (tr:trace)
  (p:principal)
  (sid sid': state_id)
  (cont:state_raw) (cont':state_raw{cont <> cont'}): 
  Lemma
  (requires
       trace_invariant tr
     /\ state_was_set tr p sid cont
     /\ state_was_set tr p sid' cont'
     /\ (let st = Some?.v (parse p_state cont) in  
        let st' = Some?.v (parse p_state cont') in  
        st.idn1 = st'.idn1
     )
  )
  (ensures
     sid = sid'
  )
  = 
   let cont'_entry = SetState p sid' cont' in
   let cont_entry = SetState p sid cont in
  
   one_is_before tr cont_entry cont'_entry;
   introduce 
      cont_entry `before_on tr` cont'_entry ==> sid = sid' 
   with _ .
     state_injective_ tr p cont_entry cont'_entry;
   introduce cont'_entry `before_on tr` cont_entry ==> sid = sid'
   with _ . 
      state_injective_ tr p cont'_entry cont_entry

