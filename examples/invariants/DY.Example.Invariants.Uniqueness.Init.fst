module DY.Example.Invariants.Uniqueness.Init

open Comparse
open DY.Core
module L = DY.Lib
open DY.Example.Invariants.Uniqueness

#set-options "--fuel 1 --ifuel 1"

let prop_state_on (#a:Type) (#state_t:Type) {|ps_state : parseable_serializeable bytes state_t|} 
  (from_state: state_t  -> a) (p: a -> bool ) (state:state_raw) : prop =
  match parse state_t state with
  | None -> True
  | Some state -> p (from_state state)

let prop_on_idn (f: nat -> bool) (state:state_raw) : prop =
  prop_state_on
      (fun state -> state.idn)
      f
      state

let forall_idns (f: nat -> bool) (sess:session_raw) : prop =
  forall_rev_list (prop_on_idn f) sess
  

let idn_does_not_appear_in_session (idn:nat) (sess:session_raw) : prop =
  forall_idns (fun idn' -> idn <> idn') sess

val max_id_in_session_largest:
  sess:session_raw ->
  Lemma 
  ( let m_idn = find_max_id_in_session sess in
    forall_idns (fun idn -> m_idn >= idn) sess
  )
let rec max_id_in_session_largest sess = 
  let m_idn = find_max_id_in_session sess in
  match sess with
  | Nil -> ()
  | Snoc rest state ->
      max_id_in_session_largest rest



let idn_does_not_appear_in_full_state (idn:nat) (fst:full_state_raw) : prop =
  forall_sessions fst (fun sid sess -> idn_does_not_appear_in_session idn sess) 


val curr_max_id_largest :
  fst:full_state_raw ->
  Lemma 
  ( let c_max = find_curr_max_id fst in
    forall_sessions fst (fun sid sess -> forall_idns (fun idn -> c_max >= idn) sess)
  )
let rec curr_max_id_largest fst =
  let c_max = find_curr_max_id fst in
  match fst with
  | [] -> ()
  | (_, sess) :: rest ->
        max_id_in_session_largest sess;
        curr_max_id_largest rest

val new_idn_does_not_appear_in_full_state: p:principal -> tr:trace ->
  Lemma
  (requires has_full_state_for tr p
  )
  (ensures (
    let (n_idn,_) = new_idn p tr in
    let fst = access_full_state tr p in
    n_idn `idn_does_not_appear_in_full_state` fst
  ))
let new_idn_does_not_appear_in_full_state p tr =
  let fst = access_full_state tr p in
  curr_max_id_largest fst

#push-options "--z3rlimit 20 --z3cliopt 'smt.qi.eager_threshold=20'"
val init_invariant: tr:trace -> p:principal ->
  Lemma 
    (requires trace_invariant tr)
    (ensures  (
      let (_,tr_out) = init p tr in
      trace_invariant tr_out
      )
    )
let init_invariant tr p =
  let (idn, tr_after_new_idn) = new_idn p tr in
  let new_state = S idn 0 in
  let new_state_b = serialize p_state new_state in
  let (new_sess_id, tr_after_new_session) = set_new_session p (serialize p_state new_state) tr_after_new_idn in
  serialize_wf_lemma p_state (is_knowable_by (principal_state_label p new_sess_id) tr_after_new_idn) new_state;

  match fst (get_full_state p tr) with
  | None -> ()
  | Some full_st ->
      forall_sessions_intro full_st
        (fun sid_i sess_i ->
           match sess_i with
           | Nil -> True
           | Snoc init_i last_i -> (
               match parse p_state last_i with
               | None -> True
               | Some last_i ->
                   if sid_i = new_sess_id
                     then last_i.idn = idn
                     else last_i.idn <> idn
             )
        )
        (fun sid_i sess_i _ ->
           match sess_i with
           | Nil -> ()
           | Snoc init_ last_i -> 
               match parse p_state last_i with
               | None -> ()
               | Some last_i -> 
                   set_new_session_new_sid p new_state_b tr;
                   full_state_mem_get_session_get_state_forall p tr;
                   assert(sid_i <> new_sess_id);
                   new_idn_does_not_appear_in_full_state p tr
        )
    


    
