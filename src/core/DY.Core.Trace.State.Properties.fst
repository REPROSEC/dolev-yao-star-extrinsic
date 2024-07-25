module DY.Core.Trace.State.Properties

open FStar.List.Tot

open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Trace.PrefixSuffix
open DY.Core.Trace.State.Aux
open DY.Core.Trace.Manipulation
open DY.Core.List

module List = FStar.List.Tot.Base



let no_set_state_entry_for_p (p:principal) (tr:trace) =
  forall sid. no_set_state_entry_for p sid tr

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


let rec zero_to_sid_mem (bound:state_id) (x :state_id{x.the_id <= bound.the_id}):
  Lemma ( ensures
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


let rec zero_to_sid_mems (bound:state_id) (sid:state_id) :
  Lemma 
  (requires
    sid `List.mem` (zero_to_sid bound)
  )
  ( ensures
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


let get_full_state_same (p:principal) (tr1:trace) (tr2:trace):
  Lemma
  (requires
      tr1 <$ tr2 /\ 
      no_set_state_entry_for_p p (tr2 `suffix_after` tr1)
    )
  (ensures get_full_state p tr1 = get_full_state p tr2)
= introduce forall sid. get_session_indexed tr1 p sid = get_session_indexed tr2 p sid
  with (
    reveal_opaque (`%get_session) get_session; 
    get_session_aux_same p sid tr1 tr2
  ); 
  compute_new_session_id_same p tr1 tr2;
  choose_equals
    (get_session_indexed tr1 p) 
    (get_session_indexed tr2 p) 
    (zero_to_sid (compute_new_session_id p tr1))
  


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



val full_state_session_lemma:
  (tr:trace) -> (p:principal) -> (sid:state_id) -> (sess:_) ->
  Lemma
  (requires
        Some? (get_full_state p tr)
      /\ (sid, sess) `List.mem` (Some?.v (get_full_state p tr))
  )
  ( ensures (
    let Some full_st = get_full_state p tr in
    get_session p sid tr = Some sess
      )
  )
let full_state_session_lemma tr p sid sess =
  mem_choose_elim 
    (get_session_indexed tr p) 
    (zero_to_sid (compute_new_session_id p tr)) 
    (sid, sess)

let full_state_some_get_session_some (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires
     Some? (get_full_state p tr)
     /\ sid `List.mem` (List.map fst (Some?.v (get_full_state p tr)))
  )
  (ensures
     Some? (get_session p sid tr)
  )
  = let Some full_st = get_full_state p tr in
    let next_sid = compute_new_session_id p tr in
    let sids = zero_to_sid next_sid in
    FStar.List.Tot.Properties.memP_map_elim fst sid full_st;
    eliminate exists sess. (sid, sess) `List.mem` full_st 
    returns Some? (get_session p sid tr)
    with _ .
      mem_choose_elim (get_session_indexed tr p) sids (sid, sess)
    


let rec get_session_grows (p:principal) (sid:state_id) (tr1 tr2:trace):
  Lemma
  ( requires tr1 <$ tr2 /\ Some? (get_session p sid tr1)
  )
  (ensures
    Some? (get_session p sid tr2)
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



let rec get_session_state_was_set (p:principal) (sid:state_id) (tr:trace):
  Lemma
  (requires Some? (get_session p sid tr))
  (ensures exists cont. state_was_set tr p sid cont )
  = match tr with
  | Nil -> ()
  | Snoc init (SetState p' sid' cont') -> (
         if p' = p && sid' = sid
         then ()
         else get_session_state_was_set p sid init
   )      
  | Snoc init _ -> 
        get_session_state_was_set p sid init



let get_session_some_full_state_some (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  ( requires Some? (get_session p sid tr)
  )
  (ensures Some? (get_full_state p tr)
  )
  =
    get_session_state_was_set p sid tr;
    eliminate exists cont . state_was_set tr p sid cont
    returns Some? (get_full_state p tr)
    with _ .
        compute_new_session_id_larger_than_id_on_trace p tr sid cont


let full_state_fst_zero_to_sid (tr:trace) (p:principal):
  Lemma
  ( requires Some? (get_full_state p tr)
  )
  (ensures (
    let Some full_st = get_full_state p tr in
    let next_sid = compute_new_session_id p tr in
    (List.map fst (full_st)) `List.subset` (zero_to_sid next_sid)
    )
  )
  =
    let Some full_st = get_full_state p tr in
    let next_sid = compute_new_session_id p tr in
  introduce forall sid. sid `List.mem` (List.map fst full_st) ==> sid `List.mem` (zero_to_sid next_sid)
  with (
    introduce _ ==> _
    with _ . (
      FStar.List.Tot.Properties.memP_map_elim fst sid full_st;
      eliminate exists sess. (sid, sess) `List.mem` full_st
      returns _
      with _ . (
      mem_choose_elim (get_session_indexed tr p) (zero_to_sid next_sid) (sid,sess)      
      )
    )
  )



let get_full_state_on_growing_traces (p:principal) (tr1 tr2:trace) (sid:state_id):
  Lemma 
  (requires
      tr1 <$ tr2
    /\ Some? (get_full_state p tr1)
    /\ sid `List.mem` (List.map fst (Some?.v (get_full_state p tr1)))
  )
  (ensures
    Some? (get_full_state p tr2) /\    
    sid `List.mem` (List.map fst (Some?.v (get_full_state p tr2)))
  )
  = 
  let Some full_st1 = get_full_state p tr1 in
 
         let new_sid1 = compute_new_session_id p tr1 in
         let new_sid2 = compute_new_session_id p tr2 in
         compute_new_session_id_grows p tr1 tr2;
         let sids1 = zero_to_sid new_sid1 in
         let sids2 = zero_to_sid new_sid2 in
         full_state_fst_zero_to_sid tr1 p;
           zero_to_sid_mems new_sid1 sid;
           zero_to_sid_mem new_sid2 sid;
         
         full_state_some_get_session_some p sid tr1;
         get_session_grows p sid tr1 tr2;
         let Some sess2 = get_session p sid tr2 in
         get_session_some_full_state_some p sid tr2;
         let Some full_st2 = get_full_state p tr2 in
         mem_choose (get_session_indexed tr2 p) sids2 sid;
         FStar.List.Tot.Properties.memP_map_intro fst (sid, sess2) full_st2
   

let rec state_was_set_full_state (tr:trace) (p:principal) (sid:state_id) (cont:bytes):
  Lemma
  (requires
    state_was_set tr p sid cont
  )
  (ensures
    Some? (get_full_state p tr) 
    /\ sid `List.mem` (List.map fst (Some?.v (get_full_state p tr)))
  )
= match tr with
  | Nil -> ()
  | Snoc init (SetState p' sid' cont') ->
      if p' = p 
        then ( 
        if sid' = sid
        then (
          compute_new_session_id_larger_than_id_on_trace p tr sid cont';
          zero_to_sid_mem (compute_new_session_id p tr) sid;
          assert(Some? (get_session p sid tr));
          let f = get_session_indexed tr p in
          let sids = (zero_to_sid (compute_new_session_id p tr)) in
          let Some full_st = get_full_state p tr in
          mem_choose f sids sid;
          FStar.List.Tot.Properties.memP_map_intro fst (sid, Some?.v (get_session p sid tr)) full_st
          )
          else (
          init_is_prefix tr;
          state_was_set_full_state init p sid cont;
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

val parse_full_state_lemma :
  (tr: trace) -> p:principal -> (sid:state_id) -> (init: _) -> (last:_) ->
  Lemma 
  (requires
       Some? (get_full_state p tr) 
     /\ (sid, (Snoc init last)) `List.mem` (Some?.v (get_full_state p tr))
  )
    ( ensures (
      let Some full_st = get_full_state p tr in
        Some?   (fst (get_state p sid tr))
      /\ Some?.v (fst (get_state p sid tr)) = last
      )

    )
let parse_full_state_lemma tr p sid init last =
  full_state_session_lemma tr p sid (Snoc init last)

val get_state_appears_in_full_state :
  tr:trace -> p:principal -> sid:state_id ->
  Lemma
  (requires
       Some? (fst (get_state p sid tr))
     /\ Some? (get_full_state p tr)
  )
  (ensures (
    let (Some state, _) = get_state p sid tr in
    let Some full_state = get_full_state p tr in
    exists init. (sid, Snoc init state) `List.mem` full_state 
  )
  )
let get_state_appears_in_full_state  tr p sid =
  let (Some state, _) = get_state p sid tr in
  let Some full_state = get_full_state p tr in
  state_was_set_full_state tr p sid state;
  FStar.List.Tot.Properties.memP_map_elim fst sid full_state;
  
  let Some session = get_session p sid tr in
  eliminate exists sess. (sid, sess) `List.mem` full_state
  returns (sid, session) `List.mem` full_state
  with _ .
    full_state_session_lemma tr p sid sess
  
val get_state_get_full_state:
  p:principal -> sid:state_id -> tr:trace ->
  Lemma 
    (requires True
    )
    (ensures (
      let (opt_state, _) = get_state p sid tr in
      let opt_full_state = get_full_state p tr in
      match opt_state with
      | None -> True
      | Some st -> 
          Some? opt_full_state
    )
    )
let get_state_get_full_state p sid tr =
    let (opt_state, _) = get_state p sid tr in
      match opt_state with
      | None -> ()
      | Some st -> state_was_set_full_state tr p sid st


let rec get_state_no_set_state_for_on_suffix_after_event
  (tr:trace) (p:principal) (sid:state_id) :
  Lemma 
  ( let (opt_cont, tr_out) = get_state p sid tr in
  match opt_cont with
    | None -> True
    | Some st -> no_set_state_entry_for p sid (tr `suffix_after_event` (SetState p sid st)) 
  )
  = reveal_opaque (`%get_state) get_state; 
  match get_state p sid tr with
  | (None, _) -> ()
  | (Some st, _) ->
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


let rec no_set_state_entry_for_on_suffix (tr:trace) (suff:trace) (p:principal) (sid:state_id):
  Lemma
  (requires tr `has_suffix` suff /\ no_set_state_entry_for p sid tr
  )
  (ensures
    no_set_state_entry_for p sid suff
  )
  = match suff with
  | Nil -> ()
  | Snoc suff_init suff_ev ->
         match tr with
         | Nil -> ()
         | Snoc tr_init tr_ev -> 
                init_is_prefix tr;
                no_set_state_entry_for_on_suffix tr_init suff_init p sid;
                assert(event_exists tr tr_ev)

