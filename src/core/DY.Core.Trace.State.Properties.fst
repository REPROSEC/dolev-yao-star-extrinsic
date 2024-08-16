module DY.Core.Trace.State.Properties

open FStar.List.Tot

open DY.Core.List
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Trace.PrefixSuffix
open DY.Core.Trace.State.Aux
open DY.Core.Trace.State.NoSetStateEntry
open DY.Core.Trace.Manipulation
open DY.Core.List

module List = FStar.List.Tot.Base
module ListProps = FStar.List.Tot.Properties



open DY.Core.Trace.Invariant

/// the session predicate remains true
/// if the trace grows
/// but there are no more state entries for the principal and the session

val session_pred_later_:
  {|cinvs: crypto_invariants |} -> {|sp:state_predicate cinvs |} ->
  tr1:trace -> tr2:trace  -> p:principal -> sid:state_id -> cont:state_raw ->
  Lemma
    (requires 
        tr1 <$ tr2 
      /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
      /\ session_pred_ tr1 (get_session_aux p sid tr1) p sid cont
    )
    (ensures session_pred_ tr2 (get_session_aux p sid tr2) p sid cont)
let session_pred_later_ #_ #sp tr1 tr2 p sid cont =
  get_session_aux_same p sid tr1 tr2;
  match get_session_aux p sid tr1 with
  | None -> ()
  | Some session ->
         sp.session_pred_grows tr1 tr2 session p sid cont

let session_pred_later {|invs:protocol_invariants|} = session_pred_later_ #invs.crypto_invs #invs.trace_invs.state_pred





(*** Properties of get_state ***)

let get_state_session_full_state_does_not_change_trace (p:principal) (sid:state_id) (tr:trace):
  Lemma
  ( let (_, tr_out_st) = get_state p sid tr in
    let (_, tr_out_sess) = get_session p sid tr in
    let (_, tr_out_fst) = get_full_state p  tr in
    tr_out_st = tr /\
    tr_out_sess = tr /\
    tr_out_fst = tr
  )
  =   reveal_opaque (`%get_state) get_state



val get_state_state_was_set :
  p:principal -> sid:state_id -> tr:trace ->
  Lemma 
  (requires Some? (fst (get_state p sid tr)))
  (ensures (
    let (Some cont, tr_out) = get_state p sid tr in
      tr == tr_out
    /\ state_was_set tr p sid cont
  ))
  [SMTPat (get_state p sid tr)]
let  get_state_state_was_set p sid tr =
  reveal_opaque (`%get_state) get_state


let rec state_was_set_get_state 
  (p:principal) (sid:state_id) (cont:state_raw) (tr:trace):
  Lemma 
  (requires state_was_set tr p sid cont)
  (ensures Some? (fst (get_state p sid tr)) )
  =   reveal_opaque (`%get_state) get_state; 
    match tr with
    | Nil -> ()
    | Snoc init (SetState p' sid' cont') ->
           if p' = p && sid' = sid 
           then ()
           else state_was_set_get_state p sid cont init
    | Snoc init _ -> state_was_set_get_state p sid cont init

let rec get_state_no_set_state_for_on_suffix_after_event
  (tr:trace) (p:principal) (sid:state_id) :
  Lemma 
  (requires Some? (fst (get_state p sid tr))
  )
  ( ensures (
    let (Some st , _) = get_state p sid tr in
    no_set_state_entry_for p sid (tr `suffix_after_event` (SetState p sid st)) 
    )
  )
= let (Some st , _) = get_state p sid tr in
  reveal_opaque (`%get_state) get_state; 
  match tr with
  | Nil -> ()
  | Snoc init (SetState p' sid' cont') -> 
         if p' = p && sid' = sid
           then ()
           else ( 
             get_state_no_set_state_for_on_suffix_after_event init p sid;
             suffix_after_event_init tr (SetState p' sid' cont')
           )
  | Snoc init ev -> 
    get_state_no_set_state_for_on_suffix_after_event init p sid;
    suffix_after_event_init tr (SetState p sid st)

(*** Properties of get_session ***)

let rec get_session_grows (p:principal) (sid:state_id) (tr1 tr2:trace):
  Lemma
  (requires tr1 <$ tr2 /\ Some? (fst (get_session p sid tr1))
  )
  (ensures
    Some? (fst (get_session p sid tr2))
  )
 = reveal_opaque (`%grows) grows; 
   norm_spec [zeta; delta_only [`%prefix]] (prefix);
   if tr1 = tr2 
   then ()
   else (
     match tr2 with
     | Nil -> ()
     | Snoc init _ -> get_session_grows p sid tr1 init
   )

(*** Relations of get_state and get_session ***)

val get_state_is_last_of_get_session:
  p:principal -> sid:state_id -> tr:trace ->
  Lemma (
    let (opt_session, _) = get_session p sid tr in
    let (opt_state, _) = get_state p sid tr in
    match opt_state with
    | None -> None? opt_session
    | Some st -> 
        Some? opt_session /\ Snoc? (Some?.v opt_session) 
        /\ (let Some (Snoc _ last) = opt_session in 
           st = last
          )
  )
  [SMTPat (get_session p sid tr); SMTPat (get_state p sid tr)]
let rec get_state_is_last_of_get_session p sid tr =
  reveal_opaque (`%get_state) (get_state);
  match tr with
  | Nil -> ()
  | Snoc init _ ->  get_state_is_last_of_get_session p sid init


let get_state_some_get_session_some (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires Some? (fst (get_state p sid tr)))
  (ensures  Some? (fst (get_session p sid tr)))
  [SMTPat (get_state p sid tr)]
  = ()


let rec get_session_some_get_state_some (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires Some? (fst (get_session p sid tr)))
  (ensures Some? (fst (get_state p sid tr)))
  = 
    reveal_opaque (`%get_state) get_state;
    match tr with
    | Nil -> ()
    | Snoc init (SetState p' sid' _) ->
           if p' = p && sid' = sid
           then ()
           else get_session_some_get_state_some p sid init
    | Snoc init _ -> get_session_some_get_state_some p sid init



let get_session_state_was_set (p:principal) (sid:state_id) (tr:trace):
  Lemma
  (requires Some? (fst (get_session p sid tr)))
  (ensures exists cont. state_was_set tr p sid cont )
  = get_session_some_get_state_some p sid tr;
    get_state_state_was_set p sid tr


(*** Relation of get_state, get_session and get_full_state ***)


/// The main relation:
/// for any pair (sid, sess) in the full state of a principal [get_full_state p],
/// we have
/// * sess is [get_session p sid]
/// * the last entry of sess is [get_state p sid]


let full_state_mem_get_session_get_state_forall (p:principal) (tr:trace):
  Lemma 
  (requires Some? (fst (get_full_state p tr)))
  (ensures (
     let (Some full_st, _) = get_full_state p tr in
     forall sid cont. (sid, cont) `List.mem` full_st ==> (
       let (session_opt, _) = get_session p sid tr in
       let (state_opt, _) = get_state p sid tr in

         Some? session_opt
       /\ (let Some sess = session_opt in
            // content stored in full state related to sid
            // is [get_session p sid]
            cont = sess
          /\ // the content stored is not empty
            ( Snoc? cont 
            /\ (let Snoc _ last = cont in
               // there is a state for p and sid on tr
               Some? state_opt 
               /\ // and this state is the last entry in the stored content
                Some?.v state_opt = last
              )
            )
         )
       )
  ))
=  let (Some full_st, _) = get_full_state p tr in
   introduce forall sid cont. (sid, cont) `List.mem` full_st ==> (
     let (session_opt, _) = get_session p sid tr in
     let (state_opt, _) = get_state p sid tr in

       Some? session_opt
     /\ (let Some sess = session_opt in
          cont = sess
        /\ ( Snoc? cont 
          /\ (let Snoc _ last = cont in
               Some? state_opt 
             /\ Some?.v state_opt = last
            )
          )
       )
    )
   with (
     introduce _ ==> _
      with _ . (
        mem_choose_elim 
          (get_session_aux_indexed tr p) 
          (zero_to_sid (compute_new_session_id p tr)) 
          (sid, cont)        
      )
   )

// corolloray of the above
// instantiated for a given state id
let full_state_some_get_session_get_state (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires
       Some? (fst (get_full_state p tr))
     /\ // the state id appears as key in the full state
       sid `List.mem` (List.map fst (Some?.v (fst (get_full_state p tr))))
  )
  (ensures (
     let (Some full_st, _) = get_full_state p tr in
     let (session_opt, _) = get_session p sid tr in
     let (state_opt, _) = get_state p sid tr in

     Some? session_opt
     /\ (let Some sess = session_opt in
        ((sid, sess) `List.mem` full_st)
        /\ ( Snoc? sess 
          /\ (let Snoc _ last = sess in
               Some? state_opt 
             /\ Some?.v state_opt = last
            )
          )
       )
   )
  )
  = let (Some full_st, _) = get_full_state p tr in
    FStar.List.Tot.Properties.memP_map_elim fst sid full_st;
    full_state_mem_get_session_get_state_forall p tr



(*** Properties of compute_new_session_id ***)

// most of them are needed for [get_full_state_on_growing_traces]

val compute_new_session_id_larger_than_id_on_trace:
  prin:principal -> tr:trace ->
  sess_id:state_id -> state_content:bytes ->
  Lemma
  (requires event_exists tr (SetState prin sess_id state_content))
  (ensures sess_id.the_id < (compute_new_session_id prin tr).the_id)
let rec compute_new_session_id_larger_than_id_on_trace prin tr sess_id state_content =
  match tr with
  | Nil -> ()
  | Snoc tr_init evt -> (
    if evt = SetState prin sess_id state_content then ()
    else (
      compute_new_session_id_larger_than_id_on_trace prin tr_init sess_id state_content
    )
  )

// the result of [compute_new_session_id] stays the same,
// if there are no more SetState entries for p on the trace
let rec compute_new_session_id_same (p:principal) (tr1 tr2:trace) :
  Lemma (
    requires
      tr1 <$ tr2 /\ 
      no_set_state_entry_for_p p (tr2 `suffix_after` tr1)
  )
  (ensures
    compute_new_session_id p tr1 = compute_new_session_id p tr2
  )
  = reveal_opaque (`%grows) grows; 
    norm_spec [zeta; delta_only [`%prefix]] (prefix);
    if tr1 = tr2 
    then ()
    else (
      match tr2 with
       | Nil -> ()
       | Snoc init (SetState p' sid' cont') -> (
           let ev = (SetState p' sid' cont') in
           assert(event_exists (tr2 `suffix_after` tr1) ev);
           suffix_after_for_prefix tr2 init tr1;
           compute_new_session_id_same p tr1 init
         )
       | Snoc init ev -> 
           suffix_after_for_prefix tr2 init tr1;
           compute_new_session_id_same p tr1 init
    )

// any number smaller than the bound,
// appears in [zero_to_sid bound]
let rec zero_to_sid_mem (bound:state_id) (x :state_id):
  Lemma
  (requires
     x.the_id <= bound.the_id
  )
  (ensures
     x `List.mem` (zero_to_sid bound)
  )
  (decreases bound.the_id)  
  = if bound.the_id = 0
    then ()
    else begin
      FStar.List.Tot.Properties.append_mem_forall (zero_to_sid {the_id = bound.the_id - 1}) [bound];
      if x = bound
      then ()
      else 
        zero_to_sid_mem ({the_id = bound.the_id -1}) x
    end

// the opposite of the above:
// any number in [zero_to_sid bound]
// is smaller than the bound
let rec zero_to_sid_mems (bound:state_id) (sid:state_id) :
  Lemma 
  (requires
     sid `List.mem` (zero_to_sid bound)
  )
  (ensures
     sid.the_id <= bound.the_id
  )
  (decreases bound.the_id)
  = if bound.the_id = 0
    then ()
    else (
      if sid = bound
      then ()
      else (
        FStar.List.Tot.Properties.append_mem_forall (zero_to_sid {the_id = bound.the_id - 1}) [bound];
        zero_to_sid_mems ({the_id =bound.the_id - 1}) sid
      )
    )

let rec compute_new_session_id_grows (p:principal) (tr1 tr2:trace):
  Lemma 
  (requires tr1 <$ tr2
  )
  (ensures
    (compute_new_session_id p tr1).the_id <= (compute_new_session_id p tr2).the_id
  )
  = reveal_opaque (`%grows) grows; 
    norm_spec [zeta; delta_only [`%prefix]] (prefix);
    if tr1 = tr2
    then ()
    else (
      match tr2 with
      | Nil -> ()
      | Snoc tr2_init tr2_ev -> compute_new_session_id_grows p tr1 tr2_init
    )



(*** More Relation on get_state, get_session and get_full_state ***)

let get_session_some_get_full_state_some (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires Some? (fst (get_session p sid tr)))
  (ensures Some? (fst (get_full_state p tr)) 
  // /\  sid `List.mem` (List.map fst (Some?.v (fst (get_full_state p tr))))
  )
  =
    get_session_state_was_set p sid tr;
    eliminate exists cont . state_was_set tr p sid cont
    returns Some? (fst (get_full_state p tr))
    with _ .
        compute_new_session_id_larger_than_id_on_trace p tr sid cont


val get_state_some_get_full_state_some:
  tr:trace -> p:principal -> sid:state_id ->
  Lemma 
  (requires Some? (fst (get_state p sid tr)))
  (ensures  Some? (fst (get_full_state p tr)))
let get_state_some_get_full_state_some tr p sid  =  
  get_session_some_get_full_state_some p sid tr


// funktioniert noch nicht so richtig
// let ad (p:principal) (sid:state_id) (tr:trace):
//   Lemma (
//       Some? (fst (get_state p sid tr )) <==> Some? (fst (get_session p sid tr))
//     /\ Some? (fst (get_session p sid tr)) <==> (Some? (fst (get_full_state p tr)) /\ sid `List.mem` (List.map fst (Some?.v (fst (get_full_state p tr)))))
//   )
// = 
//   FStar.Classical.move_requires_3 get_state_some_get_session_some p sid tr;
//   FStar.Classical.move_requires_3 get_session_some_get_state_some p sid tr;
//   FStar.Classical.move_requires_3 get_session_some_get_full_state_some p sid tr;
//   FStar.Classical.move_requires_3 full_state_some_get_session_get_state p sid tr;
//   ()
  
(*** Properties of get_full_state ***)

// the full state stays the same 
// if there are no more SetState entries for p
let get_full_state_same (p:principal) (tr1:trace) (tr2:trace):
  Lemma
  (requires
     tr1 <$ tr2 /\ 
     no_set_state_entry_for_p p (tr2 `suffix_after` tr1)
  )
  (ensures fst (get_full_state p tr1) = fst (get_full_state p tr2))
= introduce forall sid. get_session_aux_indexed tr1 p sid = get_session_aux_indexed tr2 p sid
  with (
    reveal_opaque (`%get_session) get_session; 
    get_session_aux_same p sid tr1 tr2
  ); 
  compute_new_session_id_same p tr1 tr2;
  choose_equals
    (get_session_aux_indexed tr1 p) 
    (get_session_aux_indexed tr2 p) 
    (zero_to_sid (compute_new_session_id p tr1))


let full_state_fst_zero_to_sid (tr:trace) (p:principal):
  Lemma
  (requires Some? (fst (get_full_state p tr)))
  (ensures (
     let (Some full_st,  _) = get_full_state p tr in
     let next_sid = compute_new_session_id p tr in
     (List.map fst (full_st)) `List.subset` (zero_to_sid next_sid)
  ))
  =
    let (Some full_st, _) = get_full_state p tr in
    let next_sid = compute_new_session_id p tr in
    introduce forall sid. sid `List.mem` (List.map fst full_st) ==> sid `List.mem` (zero_to_sid next_sid)
    with (
      introduce _ ==> _
      with _ . (
        FStar.List.Tot.Properties.memP_map_elim fst sid full_st;
        eliminate exists sess. (sid, sess) `List.mem` full_st
        returns _
        with _ . (
          mem_choose_elim (get_session_aux_indexed tr p) (zero_to_sid next_sid) (sid,sess)    
        )
      )
    )

// a sid stored in a full state remains in the full state when the trace grows
let get_full_state_on_growing_traces (p:principal) (tr1 tr2:trace) (sid:state_id):
  Lemma 
  (requires
       tr1 <$ tr2
     /\ Some? (fst (get_full_state p tr1))
     /\ sid `List.mem` (List.map fst (Some?.v (fst (get_full_state p tr1))))
  )
  (ensures
       Some? (fst (get_full_state p tr2))    
     /\ sid `List.mem` (List.map fst (Some?.v (fst (get_full_state p tr2))))
  )
  = 
  let (Some full_st1, _) = get_full_state p tr1 in
  let new_sid1 = compute_new_session_id p tr1 in
  let new_sid2 = compute_new_session_id p tr2 in
  compute_new_session_id_grows p tr1 tr2;
  let sids1 = zero_to_sid new_sid1 in
  let sids2 = zero_to_sid new_sid2 in
  full_state_fst_zero_to_sid tr1 p;
  zero_to_sid_mems new_sid1 sid;
  zero_to_sid_mem new_sid2 sid;

  full_state_some_get_session_get_state p sid tr1;
  get_session_grows p sid tr1 tr2;
  let (Some sess2, _) = get_session p sid tr2 in
  get_session_some_get_full_state_some p sid tr2;
  let (Some full_st2, _) = get_full_state p tr2 in
  mem_choose (get_session_aux_indexed tr2 p) sids2 sid;
  FStar.List.Tot.Properties.memP_map_intro fst (sid, sess2) full_st2
   
(*** More Relations on get_state and get_full_state ***)

let state_was_set_full_state_some (tr:trace) (p:principal) (sid:state_id) (cont:bytes):
  Lemma 
  (requires state_was_set tr p sid cont)
  (ensures Some? (fst (get_full_state p tr)))
  [SMTPat (state_was_set tr p sid cont)]
  = 
  state_was_set_get_state p sid cont tr;
  get_state_some_get_full_state_some tr p sid

let rec state_was_set_full_state (tr:trace) (p:principal) (sid:state_id) (cont:bytes):
  Lemma
  (requires state_was_set tr p sid cont )
  (ensures (
     sid `List.mem` (List.map fst (Some?.v (fst (get_full_state p tr))))
  ))
= 
  match tr with
  | Nil -> ()
  | Snoc init (SetState p' sid' cont') ->
      if p' = p 
        then ( 
          if sid' = sid
          then (
            compute_new_session_id_larger_than_id_on_trace p tr sid cont';
            zero_to_sid_mem (compute_new_session_id p tr) sid;
            assert(Some? (fst (get_session p sid tr)));
            let f = get_session_aux_indexed tr p in
            let sids = (zero_to_sid (compute_new_session_id p tr)) in
            let (Some full_st, _) = get_full_state p tr in
            mem_choose f sids sid;
            FStar.List.Tot.Properties.memP_map_intro fst (sid, Some?.v (fst (get_session p sid tr))) full_st
          )
          else (
            init_is_prefix tr;
            state_was_set_full_state init p sid cont;
            state_was_set_full_state_some init p sid cont;

            get_full_state_on_growing_traces p init tr sid
          )
        )
        else (
          init_is_prefix tr;
          get_full_state_same p init tr;
          state_was_set_full_state init p sid cont
        ) 
 | Snoc init _ -> 
     init_is_prefix tr;
     get_full_state_same p init tr;
     state_was_set_full_state init p sid cont

val get_state_appears_in_full_state :
  tr:trace -> p:principal -> sid:state_id ->
  Lemma
  (requires Some? (fst (get_state p sid tr)))
  (ensures (
     let (Some state, _) = get_state p sid tr in
   
     get_state_some_get_full_state_some tr p sid;
     let (Some full_state, _) = get_full_state p tr in

     exists init. (sid, Snoc init state) `List.mem` full_state 
  ))
let get_state_appears_in_full_state  tr p sid =
  let (Some state, _) = get_state p sid tr in

  get_state_some_get_full_state_some tr p sid;
  let (Some full_state, _) = get_full_state p tr in
  
  state_was_set_full_state tr p sid state;
  FStar.List.Tot.Properties.memP_map_elim fst sid full_state;
  full_state_some_get_session_get_state p sid tr
  

