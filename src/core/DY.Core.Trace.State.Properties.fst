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


(*** Convenience Functions to check and access state, session, and full state ***)
// those are useful in Lemma statements

// read as: "does the trace have a state for p and sid?"
// if we would use the pair (p, sid) this could be used infix:
// tr `has_state_for` (p, sid)
let has_state_for (tr:trace) (p:principal) (sid:state_id)  =
  Some? (fst (get_state p sid tr))

// if the trace has a state entry for p and sid,
// this returns that state
let access_state (tr:trace) (p:principal) (sid:state_id{has_state_for tr p sid}) = 
  Some?.v (fst (get_state p sid tr))

let has_session_for (tr:trace) (p:principal) (sid:state_id)  =
  Some? (fst (get_session p sid tr))

let access_session (tr:trace) (p:principal) (sid:state_id{has_session_for tr p sid}) = 
  Some?.v (fst (get_session p sid tr))


let has_full_state_for (tr:trace) (p:principal) =
  Some? (fst (get_full_state p tr))

let access_full_state (tr:trace) (p:principal{has_full_state_for tr p}) = 
  Some?.v (fst (get_full_state p tr))


(*** Properties of set_state ***)

let set_state_state_was_set (tr:trace) (p:principal) (sid:state_id) (cont:state_raw):
  Lemma
  ( let (_, tr_out) = set_state p sid cont tr in
    state_was_set tr_out p sid cont
  )
  = reveal_opaque (`%set_state) (set_state)
   

(*** Properties of get_state ***)

val get_state_state_was_set :
  p:principal -> sid:state_id -> tr:trace ->
  Lemma 
  (requires has_state_for tr p sid)
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
  (ensures has_state_for tr p sid)
  = reveal_opaque (`%get_state) get_state; 
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
  (requires has_state_for tr p sid)
  ( ensures (
    let st = access_state tr p sid in
    no_set_state_entry_for p sid (tr `suffix_after_event` (SetState p sid st)) 
    )
  )
= let st = access_state tr p sid in
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

val get_state_same:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma
    (requires
      tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    )
    (ensures fst (get_state p sid tr1) = fst (get_state p sid tr2))
 //   [SMTPat (tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1))]
let get_state_same p sid tr1 tr2 =
  reveal_opaque (`%get_state) get_state;
  get_state_aux_same p sid tr1 tr2



(*** Properties of get_session ***)

let rec get_session_grows (p:principal) (sid:state_id) (tr1 tr2:trace):
  Lemma
  (requires tr1 <$ tr2 /\ has_session_for tr1 p sid)
  (ensures has_session_for tr2 p sid)
 = reveal_opaque (`%grows) grows; 
   norm_spec [zeta; delta_only [`%prefix]] (prefix);
   if tr1 = tr2 
   then ()
   else (
     match tr2 with
     | Nil -> ()
     | Snoc init _ -> get_session_grows p sid tr1 init
   )

val get_session_same:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma
  (requires
    tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
  )
  (ensures fst (get_session p sid tr1) = fst (get_session p sid tr2))
let get_session_same p sid tr1 tr2 =
  get_session_aux_same p sid tr1 tr2

let rec no_set_state_entry_no_session 
  (p:principal) (sid:state_id) (tr:trace):
  Lemma
  ( requires no_set_state_entry_for p sid tr
  )
  (ensures
    Nil? (get_session_ p sid tr)
  )
  = match tr with
   | Nil -> ()
   | Snoc init _ -> 
          init_is_prefix tr;
          no_set_state_entry_no_session p sid init


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
  (requires has_state_for tr p sid)
  (ensures  has_session_for tr p sid)
  [SMTPat (get_state p sid tr)]
  = ()


let get_session_some_get_state_some (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires has_session_for tr p sid)
  (ensures has_state_for tr p sid)
  [SMTPat (get_session p sid tr)]
  = () 

(*** Relation of get_state, get_session and get_full_state ***)


/// The main relation:
/// for any pair (sid, sess) in the full state of a principal [get_full_state p],
/// we have
/// * sess is [get_session p sid]
/// * the last entry of sess is [get_state p sid]


let full_state_mem_get_session_get_state_forall (p:principal) (tr:trace):
  Lemma 
  (requires has_full_state_for tr p)
  (ensures (
     let full_st = access_full_state tr p in
     forall sid cont. (sid, cont) `List.mem` full_st ==> (
       let (session_opt, _) = get_session p sid tr in
       let (state_opt, _)   = get_state p sid tr in

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
=  let full_st = access_full_state tr p in
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


let appears_in_fsts (#a #b: eqtype) (x:a) (xs : list (a*b)) =
  x `List.mem` (List.map fst xs)



// corolloray of the above
// instantiated for a given state id
let full_state_some_get_session_get_state (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires
       has_full_state_for tr p
     /\ // the state id appears as key in the full state
       sid `appears_in_fsts` access_full_state tr p
  )
  (ensures (
     let full_st = access_full_state tr p in
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
  = let full_st = access_full_state tr p in
    FStar.List.Tot.Properties.memP_map_elim fst sid full_st;
    full_state_mem_get_session_get_state_forall p tr



(*** Properties of compute_new_session_id ***)

// most of them are needed for [get_full_state_on_growing_traces]


val compute_new_session_id_larger_than_get_state_sid:
  prin:principal -> tr:trace ->
  sess_id:state_id ->
  Lemma
  (requires has_state_for tr prin sess_id)
  (ensures sess_id.the_id < (compute_new_session_id prin tr).the_id)
let compute_new_session_id_larger_than_get_state_sid prin tr sess_id =
  get_state_state_was_set prin sess_id tr;
  eliminate exists cont. state_was_set tr prin sess_id cont
  returns sess_id.the_id < (compute_new_session_id prin tr).the_id
  with _ . compute_new_session_id_larger_than_id_on_trace prin tr sess_id cont


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



(*** Properties of set_session ***)


let new_session_new_sid (p:principal) (tr:trace):
  Lemma
  ( let (new_sid, _) = new_session_id p tr in
    no_set_state_entry_for p new_sid tr
  )
= reveal_opaque (`%new_session_id) new_session_id; 
  compute_new_session_new_sid p tr

let set_new_session_new_sid (p:principal) (cont:state_raw) (tr:trace):
  Lemma
  ( let (new_sid, tr_out) = set_new_session p cont tr in
    no_set_state_entry_for p new_sid tr
  )
  = new_session_new_sid p tr

let set_new_session_state_was_set (tr:trace) (p:principal) (cont:state_raw):
  Lemma
  ( let (sid, tr_out) = set_new_session p cont tr in
    state_was_set tr_out p sid cont
  )
  = reveal_opaque (`%set_state) (set_state)


let set_new_session_get_session
  (p: principal) (cont:state_raw) (tr:trace):
  Lemma
  ( let (new_sid, tr_out) = set_new_session p cont tr in
    let sess = get_session_aux p new_sid tr_out in
    sess = Some (Snoc Nil cont)
  )
  = reveal_opaque (`%set_state) set_state; 
   let (new_sid, tr_out) = set_new_session p cont tr in
   set_new_session_new_sid p cont tr;
   no_set_state_entry_no_session p new_sid tr

val set_new_session_invariant:
  {|invs:protocol_invariants|} ->
  prin:principal -> content:state_raw -> tr:trace ->
  Lemma
  (requires (
      let (new_sid , _)= set_new_session prin content tr in
      let sess = get_session_aux prin new_sid tr in
      let full_st = get_full_state_aux prin tr in
        trace_invariant tr
      /\ state_pred tr prin new_sid content 
      /\ session_pred_opt tr sess prin new_sid content
      /\ full_state_pred_opt tr full_st prin new_sid content
  )
  )
  (ensures (
    let (new_sid, tr_out) = set_new_session prin content tr in
    trace_invariant tr_out /\
    state_was_set tr_out prin new_sid content 
  ))
  [SMTPat (set_new_session prin content tr); SMTPat (trace_invariant #invs tr)]
let set_new_session_invariant #invs prin content tr =
  let (new_sid , tr_out) = new_session_id prin tr in
  add_event_invariant (SetState prin new_sid content) tr;
  normalize_term_spec set_state

val set_new_session_invariant_:
  {|invs:protocol_invariants|} ->
  prin:principal -> content:state_raw -> tr:trace ->
  Lemma
  (requires (
      let (new_sid , _)= set_new_session prin content tr in
      let full_st = get_full_state_aux prin tr in
        trace_invariant tr
      /\ state_pred tr prin new_sid content 
      /\ session_pred tr Nil prin new_sid content
      /\ full_state_pred_opt tr full_st prin new_sid content
  )
  )
  (ensures (
    let (new_sid, tr_out) = set_new_session prin content tr in
    trace_invariant tr_out /\
    state_was_set tr_out prin new_sid content
  ))
let set_new_session_invariant_ p cont tr =
  let (new_sid , _)= set_new_session p cont tr in
  set_new_session_new_sid p cont tr; 
  no_set_state_entry_no_session p new_sid tr

(*** More Relation on get_state, get_session and get_full_state ***)

let get_session_some_get_full_state_some (p:principal) (sid:state_id) (tr:trace):
  Lemma 
  (requires has_session_for tr p sid)
  (ensures has_full_state_for tr p)
  [SMTPat (get_session p sid tr)]
  = compute_new_session_id_larger_than_get_state_sid p tr sid


val get_state_some_get_full_state_some:
  tr:trace -> p:principal -> sid:state_id ->
  Lemma 
  (requires has_state_for tr p sid)
  (ensures  has_full_state_for tr p)
  [SMTPat (get_state p sid tr)]
let get_state_some_get_full_state_some tr p sid = ()


  
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
  with get_session_same p sid tr1 tr2; 
  compute_new_session_id_same p tr1 tr2;
  choose_equals
    (get_session_aux_indexed tr1 p) 
    (get_session_aux_indexed tr2 p) 
    (zero_to_sid (compute_new_session_id p tr1))


let full_state_fst_zero_to_sid (tr:trace) (p:principal):
  Lemma
  (requires has_full_state_for tr p)
  (ensures (
     let full_st = access_full_state tr p in
     let next_sid = compute_new_session_id p tr in
     (List.map fst (full_st)) `List.subset` (zero_to_sid next_sid)
  ))
  =
    let full_st = access_full_state tr p in
    let next_sid = compute_new_session_id p tr in
    introduce forall sid. sid `appears_in_fsts` full_st ==> sid `List.mem` (zero_to_sid next_sid)
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

// let has_full_state_has_mem (p:principal) (tr:trace):
//   Lemma 
//   (requires tr `has_full_state_for` p
//   )
//   (ensures exists sid sess. (sid, sess) `List.mem` (access_full_state tr p)
//   )
//   =()

// let has_full_state_grows (p:principal) (tr1 tr2:trace):
//   Lemma
//   (requires tr1 <$ tr2 /\ tr1 `has_full_state_for` p)
//   (ensures tr2 `has_full_state_for` p)
// = eliminate exists (sid:state_id) (sess:session_raw). (sid,sess) `List.mem` (access_full_state tr1 p)
//  returns tr2 `has_full_state_for` p
//  with _ .
//   admit()

// a sid stored in a full state remains in the full state when the trace grows
let get_full_state_on_growing_traces (p:principal) (tr1 tr2:trace) (sid:state_id):
  Lemma 
  (requires
       tr1 <$ tr2
     /\ has_full_state_for tr1 p
     /\ sid `appears_in_fsts` access_full_state tr1 p
  )
  (ensures
       has_full_state_for tr2 p
     /\ sid `appears_in_fsts` access_full_state tr2 p
  )
  = 
  let full_st1 = access_full_state tr1 p in
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
  let sess2 = access_session tr2 p sid  in
  get_session_some_get_full_state_some p sid tr2;
  let full_st2 = access_full_state tr2 p in
  mem_choose (get_session_aux_indexed tr2 p) sids2 sid;
  FStar.List.Tot.Properties.memP_map_intro fst (sid, sess2) full_st2
   
(*** More Relations on get_state and get_full_state ***)

val get_state_appears_in_full_state :
  tr:trace -> p:principal -> sid:state_id ->
  Lemma
  (requires has_state_for tr p sid)
  (ensures (
     let state = access_state tr p sid in   
     let full_state = access_full_state tr p in

     sid `appears_in_fsts` full_state /\ 
     // for some reason we need to make this explicit here,
     // i.e., the thing below is sometimes not enough
  
     (exists init. (sid, Snoc init state) `List.mem` full_state )
  ))
let get_state_appears_in_full_state  tr p sid =
  // showing sid `appears_in_fsts` full_state
     compute_new_session_id_larger_than_get_state_sid p tr sid;
     zero_to_sid_mem (compute_new_session_id p tr) sid;
     let f = get_session_aux_indexed tr p in
     let sids = (zero_to_sid (compute_new_session_id p tr)) in
     mem_choose f sids sid;

  full_state_some_get_session_get_state p sid tr


// This Lemma tells us, that whenever we get a Some for get_state or get_session, we can call [full_state_some_get_session_get_state] to know that the state and session are stored in the full state
let get_sate_session_full_state_some_equivalence (p:principal) (sid:state_id) (tr:trace):
  Lemma (
      (has_state_for tr p sid <==> has_session_for tr p sid)
    /\ (has_state_for tr p sid <==> (has_full_state_for tr p /\ sid `appears_in_fsts` access_full_state tr p))
  )
= 
  introduce has_state_for tr p sid ==> (has_full_state_for tr p /\ sid `appears_in_fsts` access_full_state tr p)
  with _ . get_state_appears_in_full_state tr p sid;
  introduce has_full_state_for tr p /\ sid `appears_in_fsts` access_full_state tr p ==> has_state_for tr p sid
  with _ . full_state_some_get_session_get_state p sid tr 
