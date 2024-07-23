module DY.Example.Invariants.Uniqueness

open Comparse
open DY.Core
module L = DY.Lib
module List = FStar.List.Tot.Base
module Trace = DY.Core.Trace.Type

/// Experimenting with the new state invariants for sessions and full states

type p_state =
 | S: idn:nat -> ctr: nat -> p_state

%splice [ps_p_state] (gen_parser (`p_state))
%splice [ps_p_state_is_well_formed] (gen_is_well_formed_lemma (`p_state))

instance parseable_serializeable_bytes_p_state: parseable_serializeable bytes p_state
 = mk_parseable_serializeable ps_p_state


type message =
  | M: alice:principal -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message
 = mk_parseable_serializeable ps_message


let max_nat (x:nat) (y:nat) : nat = max x y

let rec find_max_id_in_session (sess:session_raw) : nat = 
    match sess with
    | Nil -> 0
    | Snoc rest state -> 
        match parse p_state state with
        | None -> find_max_id_in_session rest
        | Some (S id _) -> max_nat id (find_max_id_in_session rest)

let rec find_curr_max_id (st:full_state_raw) : nat = 
    match st with
    | [] -> 0
    | (_,sess)::rest -> max_nat (find_max_id_in_session sess) (find_curr_max_id rest)

val new_idn: principal -> traceful nat
let new_idn prin =
  let* tr = get_trace in
  let opt_fst = get_full_state prin tr in
  match opt_fst with
  | None -> return (1 <: nat)
  | Some fst -> return ((find_curr_max_id fst + 1)<:nat)


val init: principal -> traceful state_id
let init prin =
  let* idn = new_idn prin in
  let new_state = S idn 0 in
  let* new_sess_id = set_new_session prin (serialize p_state new_state) in
  return new_sess_id

val next: principal -> state_id -> traceful (option unit)
let next prin sid =
  let*? curr_state = get_state prin sid in
  match parse p_state curr_state with
  | None -> return None
  | Some (S idn c) -> (
         send_msg (serialize message (M prin));*
         set_state prin sid (serialize p_state (S idn (c+1)));*
         return (Some ())
  )

let p_cinvs = {
 usages = default_crypto_usages;
 preds = default_crypto_predicates default_crypto_usages
}



let p_state_pred: state_predicate p_cinvs = {
    pred = (fun tr p sid cont -> is_knowable_by #p_cinvs (principal_state_label p sid) tr cont)
  ; session_pred = (fun tr sess prin sid cont ->
     True
    )
  ; full_state_pred = (fun tr full_st_b p sid cont -> 
      match parse p_state cont with
        | None -> False
        | Some (S the_idn _) -> begin     
            forall (i:nat{i < List.length full_st_b}). 
            match List.index full_st_b i with 
            | (_, Nil) -> True
            | (sid_i, Snoc init_i last_i) -> begin
                match parse p_state last_i with
                | None -> True
                | Some last_i ->
                    if sid_i = sid 
                      then last_i.idn = the_idn
                      else last_i.idn <> the_idn
            end
        end
      
  )
  ; pred_later = (fun t1 t2 p sid cont -> ())
  ; pred_knowable = (fun tr p sid cont -> ())
  ; session_pred_grows = (fun tr1 tr2 sess p sid cont -> ())
}

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = p_cinvs;
  trace_invs = {
    state_pred = p_state_pred;
    event_pred = (fun tr p sid ev -> True)
  }
}

// let rec full_state_event_exists (tr:trace) (p:principal) :
//   Lemma
//   (requires Some? (get_full_state p tr)
//   )
//   (ensures exists sid cont. event_exists tr (SetState p sid cont)
//   )
// = match tr with
//   | Snoc init (SetState p' sid' cont) -> 
//       if p' = p
//         then ()
//         else full_state_event_exists init p
//   | Snoc init _ -> full_state_event_exists init p

// let rec full_state_event_exists_i (tr:trace) (p:principal) (i:nat) :
//   Lemma
//   (requires 
//     Some? (get_full_state p tr)
//     /\ (let Some full_st = get_full_state p tr in
//        i < List.length full_st
//       )
//   )
//   (ensures (
//   let Some full_st = get_full_state p tr in
//   let (sid_i, _) = List.index full_st i in
//   exists cont. event_exists tr (SetState p sid_i cont)
//   )
//   )
// = let Some full_st = get_full_state p tr in
//   let (sid_i, cont_i) = List.index full_st i in
//   let sids = List.map fst full_st in
//   match tr with
//   | Snoc init (SetState p' sid' cont) -> 
//       if p' = p
//         then (
//          assume(forall curr_state. sid' `List.mem` (List.map fst (append_to curr_state sid' cont))); 
//           assert(sid' `List.mem` sids );
//           admit()
//           )
//         else full_state_event_exists_i init p i
//   | Snoc init _ -> full_state_event_exists_i init p i

let tail_is_subset (#a:eqtype) (x:a) (tl:list a) :
  Lemma 
  ( let xs = x :: tl in
    tl `List.subset` xs
  )
  = FStar.List.Tot.Properties.mem_subset tl (x :: tl)

let get_full_state_aux_step_subset (tr:trace) (p:principal) (curr_state: full_state_raw) (ev:trace_event{event_exists tr ev}):
  Lemma
  (curr_state `List.subset` get_full_state_aux_step p tr curr_state ev
  )
= match ev with
  | (SetState p' sid' cont') -> (
      if p' = p  
      then (
          if sid' `List.mem` (List.map fst curr_state)
          then ()
          else (
            state_was_set_get_session_some p sid' cont' tr;
            let Some sess = get_session p sid' tr in
            let new_state = (sid', sess) :: curr_state in
            FStar.List.Tot.Properties.mem_subset curr_state ((sid', sess) :: curr_state)
          )
      )
      else ()
  )
  | _ ->  () 



// let rec get_full_state_on_grows (tr1:trace) (tr2:trace{tr1 <$ tr2}) (p:principal):
//   Lemma
//   (requires
//     Some? (get_full_state p tr1)
//   )
//   (ensures
//     Some? (get_full_state p tr2)
//   )
//   = 
//   reveal_opaque (`%grows) grows; 
//   norm_spec [zeta; delta_only [`%prefix]] (prefix);
//   match tr2 with
//   | Nil -> assert(Nil? tr1)
//   | Snoc init (SetState p' sid' cont') ->
//       if Trace.length tr1 = Trace.length tr2
//         then ()
//         else (
//           if p' = p
//           then  admit()
//           else get_full_state_on_grows tr1 init p
//         )
//   | Snoc init _ -> (
//       if Trace.length tr1 = Trace.length tr2
//         then ()
//         else get_full_state_on_grows tr1 init p
//     )

let get_full_state_aux_step_state_was_set (p:principal) (sid:state_id) (cont:bytes) (tr:trace) (curr_state:full_state_raw) (ev:trace_event{event_exists tr ev}) :
  Lemma(
    requires ev = SetState p sid cont //state_was_set tr p sid cont
  )
  (ensures
      sid `List.mem` (List.map fst (get_full_state_aux_step p tr curr_state ev) )
  )
=  ()



// let rec get_full_state_aux_step_state_was_set_ (p:principal) (sid:state_id) (cont:bytes) (tr:trace) :
//   Lemma(
//     requires state_was_set tr p sid cont
//   )
//   (ensures
//       sid `List.mem` (List.map fst (get_full_state_aux p tr) )
//   )
// =  match tr with
// | Nil -> ()
// | Snoc init last ->
//     match last with
//     | SetState p' sid' cont' -> admit()
//     | _ -> get_full_state_aux_step_state_was_set_ p sid cont init; 
//         assert(get_full_state_aux p tr = get_full_state_aux_step p tr ( get_full_state_aux p init ) last)

let append_subset (#a:eqtype) (xs:list a) (ys: list a):
  Lemma (
    xs `List.subset` (xs @ ys)
    /\ ys `List.subset` (xs @ ys)
    )
  = FStar.List.Tot.Properties.append_mem_forall xs ys

let concatMap_subset_tail (#a #b:eqtype) (f: a -> list b) (xs: list a{Cons? xs}):
  Lemma(
    let hd::tl = xs in
    List.concatMap f tl `List.subset` List.concatMap f xs
  )
  =
  let hd::tl = xs in 
  assert(List.concatMap f xs = f hd @ List.concatMap f tl);
  append_subset (f hd) (List.concatMap f tl)

let rec mem_concatMap (#a #b:eqtype) (f: a -> list b) (xs: list a) (x:a):
  Lemma 
  (requires
    x `List.mem` xs /\
    ~(List.isEmpty (f x) )
  )
  (ensures 
   f x `List.subset` List.concatMap f xs 
  ) 
  = match xs with
  | [] -> ()
  | hd :: tl -> 
       if hd = x
       then append_subset (f hd) (List.concatMap f tl)
       else 
         mem_concatMap f tl x;
         concatMap_subset_tail f xs

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
       | Snoc init ev -> 
           assert(event_exists (tr2 `suffix_after` tr1) ev);
           suffix_after_for_prefix tr2 init tr1;
           compute_new_session_id_same p tr1 init
    )


let rec concatMap_equals (#a #b:eqtype) (f g: a -> list b) (xs : list a) :
  Lemma (
  requires
    forall x. x `List.mem` xs ==> f x = g x
  )
  (ensures
    List.concatMap f xs = List.concatMap g xs
  )
  = match xs with
  | [] -> ()
  | hd :: tl -> concatMap_equals f g tl

let get_full_state_same (p:principal) (tr1:trace) (tr2:trace):
  Lemma
  (requires
      tr1 <$ tr2 /\ 
      no_set_state_entry_for_p p (tr2 `suffix_after` tr1)
    )
  (ensures get_full_state p tr1 = get_full_state p tr2)
= introduce forall sid. get_session_list tr1 p sid == get_session_list tr2 p sid
  with (
    reveal_opaque (`%get_session) get_session; 
    get_session_aux_same p sid tr1 tr2
  ); 
  compute_new_session_id_same p tr1 tr2;
  concatMap_equals 
    (get_session_list tr1 p) 
    (get_session_list tr2 p) 
    (zero_to_sid (compute_new_session_id p tr1))


let get_full_state_on_growing_traces (p:principal) (tr1 tr2:trace) (sid:state_id):
  Lemma 
  (requires
    tr1 <$ tr2
    /\ Some? (get_full_state p tr1)
  )
  (ensures
    Some? (get_full_state p tr2) /\
    sid `List.mem` (List.map fst (Some?.v (get_full_state p tr1)))
    ==>
    sid `List.mem` (List.map fst (Some?.v (get_full_state p tr2)))
  )
  = admit()

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
          let f = get_session_list tr p
        in
        let sids = (zero_to_sid (compute_new_session_id p tr)) in
          let Some full_st = get_full_state p tr in
          mem_concatMap f sids sid;
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

val full_state_session_lemma:
  (tr:trace) -> (p:principal) -> (i:nat) ->
  Lemma(
    match get_full_state p tr with 
      | None -> True
      | Some full_st -> begin
          if i >= List.length full_st
            then True
            else begin
              let (sid_i, sess_i) = List.index full_st i in
              get_session p sid_i tr = Some sess_i
            end
      end
      
  )
let rec full_state_session_lemma tr p i =
    match get_full_state p tr with 
      | None -> ()
      | Some full_st -> begin
          if i >= List.length full_st
            then ()
            else begin
              let (sid_i, sess_i) = List.index full_st i in
              let Snoc init last = tr in
              match last with
              | SetState p' sid' cont' ->
                  if sid' = sid_i
                    then admit()
                    else (
                      
                      init_is_prefix tr;
                      get_session_aux_same p sid_i init tr;
                      assert(get_session p sid_i tr = get_session p sid_i init);
                      full_state_session_lemma init p i;
                      assume(List.index full_st i = List.index (Some?.v (get_full_state p init)) i);
                      assert(Some sess_i = get_session p sid_i init);
                      admit()
                    )
              | _ -> full_state_session_lemma init p i
            end
      end

val parse_full_state_lemma :
  (tr: trace) -> p:principal -> (i:nat) ->
  Lemma 
    (
      match get_full_state p tr with 
      | None -> True
      | Some full_st -> begin
          if i >= List.length full_st
            then True
            else begin
                   match List.index full_st i with
                   | (_, Nil) -> True
                   | (sid_i, (Snoc init_i last_i)) -> begin
                         Some?   (fst (get_state p sid_i tr))
                       /\ Some?.v (fst (get_state p sid_i tr)) = last_i
                   end
            end
      end
      
    )



let rec parse_full_state_lemma tr p i =
  reveal_opaque (`%get_state) get_state;
      match get_full_state p tr with 
      | None -> ()
      | Some full_st -> begin
        assert(full_st = get_full_state_aux p tr []);
        assert(~ (Nil? tr));
          if i >= List.length full_st
            then ()
            else begin
                   match List.index full_st i with
                   | (_, Nil) -> ()
                   | (sid_i, (Snoc init_i last_i)) -> begin
                       match tr with
                       | Snoc init (SetState p' sid' cont') ->
                              if p' = p
                                then begin
                                  if sid' = sid_i
                                    then (
                                      assert(Some?.v (fst (get_state p sid_i tr)) = cont');
                                      assert(last_i = cont');
                                      admit()
                                    )
                                    else admit()
                                end
                                else parse_full_state_lemma init p i
                       | Snoc init _ -> parse_full_state_lemma init p i                       
                   end
            end
      end 

val get_state_appears_in_full_state :
  tr:trace -> p:principal -> sid:state_id ->
  Lemma
  (
    match get_state p sid tr with
    | (None, _) -> True
    | (Some state, _) ->
        match get_full_state p tr with
        | None -> True
        | Some full_state ->
            exists i init . List.index full_state i = (sid, Snoc init state)
  )
let get_state_appears_in_full_state  tr p sid = admit()


val state_was_set_full_state_some:
  tr:trace -> p:principal -> sid:state_id -> cont:state_raw ->
  Lemma 
    (requires
      state_was_set tr p sid cont
    )
    (ensures
      Some? (get_full_state p tr)
    )
let rec state_was_set_full_state_some tr p sid cont =
  match tr with
  | Nil -> ()
  | Snoc init (SetState p' sid' cont') -> 
      if p' = p && sid' = sid && cont' = cont
        then (
        admit()
        // append_to_non_empty sid cont;
        // assume(forall curr_state. [] <> curr_state ==> get_full_state_aux p tr curr_state <> [])
        )
        else admit()
  | Snoc init _ -> state_was_set_full_state_some init p sid cont

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
      | Some st -> state_was_set_full_state_some tr p sid st


let rec prefix_including_event (tr:trace) (the_ev:trace_event{event_exists tr the_ev}) =
  match tr with
  | Snoc init ev ->
      if ev = the_ev 
        then tr
        else init `prefix_including_event` the_ev

let rec prefix_including_event_is_prefix (tr:trace) (the_ev:trace_event{event_exists tr the_ev}) :
  Lemma (tr `prefix_including_event` the_ev <$ tr)
  [SMTPat (tr `prefix_including_event` the_ev)] =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr with
  | Nil -> ()
  | Snoc init ev ->
         if ev = the_ev
           then ()
           else
             prefix_including_event_is_prefix init the_ev

let suffix_after_event (tr:trace) (ev:trace_event{event_exists tr ev}) =
  let tr_before = tr `prefix_including_event` ev in
  tr `suffix_after` tr_before

let rec suffix_after_event_init
  (tr:trace{Snoc? tr}) (the_ev:trace_event{event_exists tr the_ev})
  :Lemma 
    ( let Snoc init ev = tr in
      if the_ev <> ev
        then tr `suffix_after_event` the_ev = Snoc (init `suffix_after_event` the_ev) ev
        else True
    )
= let Snoc init ev = tr in
  if the_ev <> ev
    then
      suffix_after_event_init init the_ev
    else ()

//open DY.Core.Trace.Manipulation



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
           else ( get_state_no_set_state_for_on_suffix_after_event init p sid;
           suffix_after_event_init tr (SetState p sid st)
           )
  | Snoc init ev -> 
    get_state_no_set_state_for_on_suffix_after_event init p sid;
    suffix_after_event_init tr (SetState p sid st)

let rec has_suffix (tr:trace) (suff:trace) =
  match suff with
  | Nil -> true
  | Snoc suff_init suff_ev ->
      match tr with
      | Nil -> false
      | Snoc tr_init tr_ev ->
          suff_ev = tr_ev && (has_suffix tr_init suff_init)

let _ = 
  let ev1 = Corrupt "p" {the_id = 1} in 
  let ev2 = Corrupt "p" {the_id = 2} in 
  let ev3 = Corrupt "p" {the_id = 3} in 
  let tr = Snoc (Snoc (Snoc Nil ev1) ev2) ev3 in
  let tr' = Snoc (Snoc Nil ev2) ev3 in
  assert(tr `has_suffix` tr')

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

let rec suffix_after_is_suffix (tr:trace) (pref:trace{pref <$ tr}):
  Lemma
  (tr `has_suffix` (tr `suffix_after` pref)
  )
  [SMTPat (tr `has_suffix` (tr `suffix_after` pref))]
  =
  let suff = tr `suffix_after` pref in
  match suff with
  | Nil -> ()
  | Snoc suff_init suff_ev ->
         match tr with
         | Nil -> ()
         | Snoc tr_init tr_ev -> 
                assert(suff_ev = tr_ev);
                init_is_prefix tr;
                reveal_opaque (`%grows) grows; 
                suffix_after_is_suffix (tr_init) pref



let rec suffixes_ (tr:trace) (suff1:trace) (suff2:trace):
  Lemma
  (requires
      tr `has_suffix` suff1
    /\ tr `has_suffix` suff2
    /\ Trace.length suff1 >= Trace.length suff2
  )
  (ensures
        suff1 `has_suffix` suff2 
  )
  = match suff2 with
  | Nil -> ()
  | Snoc init2 last2 -> 
      let Snoc init1 last1 = suff1 in
      let Snoc init last = tr in 
      suffixes_ init init1 init2

let suffixes (tr:trace) (suff1:trace) (suff2:trace):
  Lemma
  (requires
      tr `has_suffix` suff1
    /\ tr `has_suffix` suff2
  )
  (ensures
        suff1 `has_suffix` suff2 
      \/ suff2 `has_suffix` suff1
  )
  = if Trace.length suff1 >= Trace.length suff2
       then suffixes_ tr suff1 suff2
       else suffixes_ tr suff2 suff1
  
let nil_grows (tr:trace):
  Lemma (Nil <$ tr)
  [SMTPat (Nil <$ tr)]
  = reveal_opaque (`%grows) grows

let rec suffix_after_nil (tr:trace):
  Lemma (tr `suffix_after` Nil = tr)
  [SMTPat (tr `suffix_after` Nil)]
  = match tr with
    | Nil -> ()
    | Snoc init ev -> suffix_after_nil init

let prepend  (ev:trace_event) (tr:trace) =
  (Snoc Nil ev) `trace_concat` tr



let rec event_splits_trace (tr:trace) (ev:trace_event{event_exists tr ev}):
  Lemma
  ( let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    tr = tr_before `trace_concat` (prepend ev tr_after)
  )
  = let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    match tr with
    | Nil -> ()
    | Snoc tr_init tr_last ->
        if tr_last = ev
          then ()
          else event_splits_trace tr_init ev
        

// let trace_concat_grows_ (tr1:trace) (tr2:trace):
//   Lemma (tr1 <$ tr1 `trace_concat` tr2)
//   [SMTPat (tr1 <$ (tr1 `trace_concat` tr2) )]
//   = trace_concat_grows tr1 tr2

let suffix_after_snoc (init:trace) (ev:trace_event) (pref:trace{pref <$ init}):
  Lemma
  ( reveal_opaque (`%grows) grows; 
    norm_spec [zeta; delta_only [`%prefix]] (prefix);

    (Snoc init ev) `suffix_after` pref = Snoc ( init `suffix_after` pref ) ev
  )
= normalize_term_spec suffix_after

let rec suffix_after_concat_ (pref:trace) (suff:trace):
  Lemma 
  ( let tr = pref `trace_concat` suff in
    trace_concat_grows pref suff;
    tr `suffix_after` pref = suff
  )
  = 
  let tr = pref `trace_concat` suff in
  match suff with
  | Nil -> ()
  | Snoc suff_init suff_ev ->
         suffix_after_concat_ pref suff_init;
         trace_concat_grows pref suff_init;
         suffix_after_snoc ( pref `trace_concat` suff_init  ) suff_ev pref

let suff_after_before_event_is_suff_at_event (tr:trace) (ev:trace_event{event_exists tr ev}):
  Lemma
  ( let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    tr `suffix_after` tr_before = (Snoc Nil ev) `trace_concat` tr_after
  )
  = let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    event_splits_trace tr ev;
    suffix_after_concat_ tr_before (prepend ev tr_after)
    

#push-options "--z3rlimit 50 " //--z3cliopt 'smt.qi.eager_threshold=50'"
val next_full_state_pred:
  tr:trace -> p:principal -> sid:state_id ->
  Lemma 
    (requires trace_invariant tr)
    (ensures  (
      let (_,tr_out) = next p sid tr in
       match get_state p sid tr with
  | (None, _) -> True
  | (Some oldst_b, _) -> (
      match parse p_state oldst_b with
      | None -> True
      | Some (S idn c) -> (          
          let msg = M p in
          let msg_b = serialize message msg in
          let (_, tr_after_msg) = send_msg msg_b tr in

          let next_state = S idn (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_msg in
           match (get_full_state p tr_after_msg) with
          | None -> True
          | Some full_st_b -> full_state_pred tr_after_msg full_st_b p sid next_state_b
      )
    )
    ))
let next_full_state_pred tr p sid = 
  match get_state p sid tr with
  | (None, _) -> ()
  | (Some oldst_b, _) -> (
      match parse p_state oldst_b with
      | None -> ()
      | Some (S idn c) -> (          
          let msg = M p in
          let msg_b = serialize message msg in
          let (_, tr_after_msg) = send_msg msg_b tr in
          serialize_wf_lemma message (is_publishable tr) msg;
          assert(trace_invariant tr_after_msg);

          let next_state = S idn (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_msg in
          
          match (get_full_state p tr_after_msg) with
          | None -> ()
          | Some full_st_b -> begin
              introduce forall (i:nat{i < List.length full_st_b}). 
                match List.index full_st_b i with 
                | (_, Nil) -> True
                | (sid_i, Snoc init_i last_i) -> (
                    match parse p_state last_i with
                    | None -> True
                    | Some last_i ->
                        if sid_i = sid 
                          then last_i.idn = idn
                          else last_i.idn <> idn
                  )
              with begin
                match List.index full_st_b i with 
                  | (_, Nil) -> ()
                  | (sid_i, (Snoc init_i last_i_b)) ->
                       match parse p_state last_i_b with
                       | None -> ()
                       | Some last_i -> 
                           parse_full_state_lemma tr_after_msg p i;
                           get_state_aux_same p sid_i tr tr_after_msg;    
                           reveal_opaque (`%get_state) (get_state);
                           if sid_i = sid
                           then assert(last_i = S idn c)
                           else begin
                             let (Some state_i, _) =  get_state p sid_i tr_after_msg in
                             assert(state_i = last_i_b );
                             let oldst_entry = SetState p sid oldst_b in
                             let tr_after_oldst = tr `suffix_after_event` (SetState p sid oldst_b) in
                             let last_i_entry = SetState p sid_i last_i_b in
                             let tr_after_last_i = (tr `suffix_after_event` (SetState p sid_i last_i_b) ) in
                             
                             if tr_after_oldst `has_suffix` tr_after_last_i // last_i after oldst on tr
                             then (
                               get_state_no_set_state_for_on_suffix_after_event tr p sid;
                               no_set_state_entry_for_on_suffix tr_after_oldst tr_after_last_i p sid;
                               assert(no_set_state_entry_for p sid tr_after_last_i);
                               let tr_before_last_i = tr `prefix_before_event` (SetState p sid_i last_i_b) in
                               suff_after_before_event_is_suff_at_event tr last_i_entry;
                               no_set_state_entry_for_concat p sid (Snoc Nil (SetState p sid_i last_i_b)) tr_after_last_i;
                               get_state_aux_same p sid tr_before_last_i tr;
                                 assert((Some oldst_b, tr_before_last_i) = get_state p sid tr_before_last_i);
                                 match get_full_state p tr_before_last_i with
                                 | None -> get_state_get_full_state p sid tr_before_last_i
                                 | Some full_state_before_last_i -> 
                                     prefix_before_event_invariant tr_after_msg (SetState p sid_i last_i_b);
                                     assert(global_state_pred tr_before_last_i p sid_i last_i_b);
                                     get_state_appears_in_full_state tr_before_last_i p sid
                             )
                             else ( // oldst after last_i on tr
                             // admit()
                               suffixes tr tr_after_last_i tr_after_oldst;
                               assert(tr_after_last_i `has_suffix` tr_after_oldst);
  
                               get_state_no_set_state_for_on_suffix_after_event tr p sid_i;
                               no_set_state_entry_for_on_suffix tr_after_last_i tr_after_oldst p sid_i;
                               let tr_before_old = tr `prefix_before_event` oldst_entry in                               
                               suff_after_before_event_is_suff_at_event tr oldst_entry;
                               no_set_state_entry_for_concat p sid_i (Snoc Nil oldst_entry) tr_after_oldst;
                               get_state_aux_same p sid_i tr_before_old tr;
                               let (Some state_i_before_old, _) = get_state p sid_i tr_before_old in
                               assert(state_i_before_old = state_i);
                               match get_full_state p tr_before_old with
                               | None -> get_state_get_full_state p sid_i tr_before_old
                               | Some full_state_before_old -> 
                                      assert(global_state_pred tr_before_old p sid oldst_b);
                                      get_state_appears_in_full_state tr_before_old p sid_i  
                             )
                           end
              end;
            ()
            end;
          ()
        )
    )

#push-options "--z3rlimit 25"
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
      | Some (S idn c) -> (          
          let msg = M p in
          let msg_b = serialize message msg in
          let (_, tr_after_msg) = send_msg msg_b tr in

          let next_state = S idn (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_msg in
          
          serialize_wf_lemma message (is_publishable tr) msg;

          serialize_wf_lemma p_state (is_knowable_by (principal_state_label p sid) tr_after_msg) next_state;

          next_full_state_pred tr p sid
        )
    )
#pop-options

let rec forall_rev_list (#a:Type) (p: a -> prop) (xs: rev_list a) : prop =
  match xs with
  | Nil -> True
  | Snoc xs x -> p x /\ forall_rev_list p xs

let forall_rev_list_snoc (#a:Type) (p: a -> prop) (xs: rev_list a) (y: a {p y}) :
  Lemma
  (requires forall_rev_list p xs)
  (ensures forall_rev_list p (Snoc xs y))
= ()

let rec forall_rev_list_implies (#a:Type) (p:a -> prop) (q:a -> prop {forall x . p x ==> q x}) (xs: rev_list a) :
  Lemma (forall_rev_list p xs ==> forall_rev_list q xs)
  = match xs with
    | Nil -> ()
    | Snoc xs s -> forall_rev_list_implies p q xs

let compare_state_on_idn (f: nat -> bool) (state:state_raw) : prop =
      match parse p_state state with
      | None -> True
      | Some (S idn' _ ) -> f idn'


let compare_idns (f: nat -> bool) (sess:session_raw) : prop =
  forall_rev_list (compare_state_on_idn f) sess
  

let idn_does_not_appear_in_session (idn:nat) (sess:session_raw) : prop =
  compare_idns (fun idn' -> idn <> idn') sess
  // forall_rev_list 
  //       (fun state ->
  //     match parse p_state state with
  //     | None -> True
  //     | Some (S idn' _ ) -> idn <> idn'
  //     )
  // sess

val max_id_in_session_largest:
  sess:session_raw ->
  Lemma 
  ( let m_idn = find_max_id_in_session sess in
    compare_idns (fun idn -> m_idn >= idn) sess
    // forall_rev_list
    //   (fun state ->
    //   match parse p_state state with
    //   | None -> True
    //   | Some (S idn _ ) -> m_idn >= idn
    //   )
    //   sess
  )
let rec max_id_in_session_largest sess = 
  let m_idn = find_max_id_in_session sess in
  let p : (state_raw -> prop) = 
    compare_state_on_idn (fun idn -> m_idn >= idn)
  // (fun state ->
  //     match parse p_state state with
  //     | None -> True
  //     | Some (S idn _ ) -> m_idn >= idn
  //     ) 
  in
  match sess with
  | Nil -> ()
  | Snoc rest state ->
      let m_idn_rest = find_max_id_in_session rest in
      max_id_in_session_largest rest;
      forall_rev_list_implies
        (compare_state_on_idn (fun idn -> m_idn_rest >= idn))
        p 
        rest


val l :
  (idn:nat) -> sess : session_raw ->
  Lemma 
  (requires
    compare_idns (fun idn' ->  idn <> idn')
    // forall_rev_list 
    //     (fun state ->
    //   match parse p_state state with
    //   | None -> True
    //   | Some (S idn' _ ) -> idn <> idn'
    //   )
  sess
  )
  (ensures
      idn_does_not_appear_in_session idn sess
  )
let l idn sess = ()

val max_id_plus_one_in_session_does_not_appear_in_session:
  sess:session_raw ->
  Lemma 
  ( let m_idn = find_max_id_in_session sess in
    idn_does_not_appear_in_session (m_idn + 1) sess
  )
let max_id_plus_one_in_session_does_not_appear_in_session sess = 
  let m_idn = find_max_id_in_session sess in
  let n_idn : nat = m_idn + 1 in
  let p : (state_raw -> prop) = 
    compare_state_on_idn (fun idn -> n_idn <> idn)
  // (fun state ->
  //         match parse p_state state with
  //         | None -> True
  //         | Some (S idn _ ) -> n_idn <> idn
  //       ) 
  in  
  // let open FStar.Tactics in
  // assert(idn_does_not_appear_in_session n_idn sess) by begin
  // FStar.Tactics.specialize (idn_does_not_appear_in_session n_idn sess) [`%idn_does_not_appear_in_session] ();
//     norm [delta_only [`%(idn_does_not_appear_in_session)]; zeta; iota];
// //    unfold_def (`idn_does_not_appear_in_session);
//     squash_intro();
//     dump "";
//     let b = nth_binder (-1) in
//     exact b;
// //    assumption();
  //   ()
  // end;
  max_id_in_session_largest sess;
  forall_rev_list_implies
    (compare_state_on_idn (fun idn -> m_idn >= idn))
    // (fun state ->
    //    match parse p_state state with
    //    | None -> True
    //    | Some (S idn _ ) -> m_idn >= idn
    // ) 
    p
    sess;      
  l n_idn sess

let rec forall_sessions (f: session_raw -> prop) (fst:full_state_raw) : prop =
  match fst with
  | [] -> True
  | (_, sess) :: rest -> f sess /\ forall_sessions f rest


let rec forall_sessions_implies (p: session_raw -> prop) (q:session_raw -> prop {forall x. p x ==> q x}) (fst:full_state_raw) :
  Lemma (forall_sessions p fst ==> forall_sessions q fst)
  = match fst with
  | [] -> ()
  | (_, sess) :: rest -> forall_sessions_implies p q rest

let idn_does_not_appear_in_full_state (idn:nat) (fst:full_state_raw) : prop =
  forall_sessions (idn_does_not_appear_in_session idn) fst
  // match fst with
  // | [] -> True
  // | (_, sess) :: rest -> idn_does_not_appear_in_session idn sess /\ idn_does_not_appear_in_full_state idn rest


val curr_max_id_largest :
  fst:full_state_raw ->
  Lemma 
  (  let c_max = find_curr_max_id fst in
    forall_sessions (compare_idns (fun idn -> c_max >= idn)) fst    
  )
let rec curr_max_id_largest fst =
  let c_max = find_curr_max_id fst in
  match fst with
  | [] -> ()
  | (_, sess) :: rest ->
        let max_in_sess = find_max_id_in_session sess in
        max_id_in_session_largest sess;
        assert(compare_idns (fun idn -> max_in_sess >= idn) sess);
        assert(c_max >= max_in_sess);
        forall_rev_list_implies
          (compare_state_on_idn (fun idn -> max_in_sess >= idn))
          (compare_state_on_idn (fun idn -> c_max >= idn))
        sess;
        assert(compare_idns (fun idn -> c_max >= idn) sess);

        let c_max_rest = find_curr_max_id rest in
        assert(c_max >= c_max_rest);
        let p = (compare_state_on_idn (fun idn -> c_max_rest >= idn) ) in
        let q = (compare_state_on_idn (fun idn -> c_max >= idn) ) in
        assert(forall s.
          (compare_state_on_idn (fun idn -> c_max_rest >= idn) ) s
          ==>
          (compare_state_on_idn (fun idn -> c_max >= idn) ) s 
          );
        introduce forall s.
          forall_rev_list (compare_state_on_idn (fun idn -> c_max_rest >= idn) ) s
          ==> 
          forall_rev_list
          (compare_state_on_idn (fun idn -> c_max >= idn) ) s 
        with  forall_rev_list_implies p q s
        ;
        forall_sessions_implies
          (compare_idns (fun idn -> c_max_rest >= idn))
          (compare_idns (fun idn -> c_max >= idn))
        rest;
        curr_max_id_largest rest;
        assert(forall_sessions (compare_idns (fun idn -> c_max >= idn)) rest)

val l_does_not_appear_in_full_state :
  (idn:nat) -> (fst:full_state_raw) ->
  Lemma 
    (requires
      forall_sessions (compare_idns (fun idn' -> idn <> idn')) fst
    )
    (ensures
      idn_does_not_appear_in_full_state idn fst
    )
let l_does_not_appear_in_full_state idn fst =
  forall_sessions_implies
    (compare_idns (fun idn' -> idn <> idn'))
    (idn_does_not_appear_in_session idn)
    fst

val curr_max_id_plus_one_does_not_appear_in_full_state: (fst:full_state_raw) ->
  Lemma
  ( let c_max = find_curr_max_id fst in
    idn_does_not_appear_in_full_state (c_max + 1) fst
  )
let curr_max_id_plus_one_does_not_appear_in_full_state fst = 
  let c_max = find_curr_max_id fst in
  let n_idn : nat = c_max + 1 in
  curr_max_id_largest fst;
  let p = (compare_state_on_idn (fun idn -> c_max >= idn) ) in
  let q = (compare_state_on_idn (fun idn -> n_idn <> idn) ) in
  introduce forall s.
          forall_rev_list p s
          ==> 
          forall_rev_list
          q s 
        with  forall_rev_list_implies p q s
        ;
  forall_sessions_implies
    (compare_idns (fun idn -> c_max >= idn))
    (compare_idns (fun idn -> n_idn <> idn))
    fst;
  assert(forall_sessions (compare_idns (fun idn -> n_idn <> idn)) fst);
  l_does_not_appear_in_full_state n_idn fst

val new_idn_does_not_appear_in_full_state: p:principal -> tr:trace ->
  Lemma
    ( let (n_idn,_) = new_idn p tr in
      let opt_fst = get_full_state p tr in
      match opt_fst with
      | None -> True
      | Some fst -> n_idn `idn_does_not_appear_in_full_state` fst
    )
let new_idn_does_not_appear_in_full_state p tr =
  let (n_idn,_) = new_idn p tr in
  let opt_fst = get_full_state p tr in
    match opt_fst with
    | None -> ()
    | Some fst ->
           curr_max_id_plus_one_does_not_appear_in_full_state fst


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
  let (new_sess_id, tr_after_new_session) = set_new_session p (serialize p_state new_state) tr_after_new_idn in
  //compute_new_session_id_correct p tr _ _;
  serialize_wf_lemma p_state (is_knowable_by (principal_state_label p new_sess_id) tr_after_new_idn) new_state;
  admit()
