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


let rec parse_session session_b : option (rev_list p_state)=
  match session_b with
  | Nil -> Some Nil
  | Snoc rest state ->
      let? st = parse #bytes p_state state in
      let? rest = parse_session rest in
      Some (Snoc rest st)

let rec parse_full_state (fst_b: full_state_raw ) : list (state_id * option (rev_list p_state)) =
  match fst_b with
  | [] -> []
  | Cons (sid, sess_b) rest ->
         (sid, parse_session sess_b) :: parse_full_state rest

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
                       Some? (fst (get_state p sid_i tr))
                       /\ Some?.v (fst (get_state p sid_i tr)) = last_i
                   end
            end
      end
      
    )
let parse_full_state_lemma tr p i =
      admit()


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

let rec forall_rev_list_bool (#a:Type) (p: a -> bool) (xs: rev_list a) : bool =
  match xs with
  | Nil -> true
  | Snoc xs x -> p x && forall_rev_list_bool p xs


val no_set_state_entry_for_bool:
  principal -> state_id -> trace -> bool
let no_set_state_entry_for_bool p sid tr = 
  forall_rev_list_bool
    (fun tr_ev ->
    match tr_ev with
    | SetState p' sid' _ -> p' <> p || sid' <> sid
    | _ -> true
    )
    tr

val no_set_state_entry_for_bool_prop:
  p:principal -> sid:state_id -> tr:trace -> 
  Lemma 
    (
      no_set_state_entry_for_bool p sid tr
   <==>
      no_set_state_entry_for p sid tr
    )
let no_set_state_entry_for_bool_prop p sid tr = admit()

// val lemma1:
//   tr:trace -> p:principal -> sid:state_id -> idn:nat ->
//   full_st:full_state_raw ->
//   i:nat{i < List.length full_st} ->
//   sid_i:state_id -> init_i:session_raw -> last_i:state_raw ->
//   tr1:trace{tr1 <$ tr} -> tr2:trace{tr <$ tr2} ->
//   Lemma
//     (requires
//       trace_invariant tr
//       /\ List.index full_st i = (sid_i, Snoc init_i last_i)
//       /\ sid_i <> sid
//       /\ no_set_state_entry_for p sid_i (tr2 `suffix_after` tr1)
//     )
//     (ensures (
//       match parse p_state last_i with
//       | None -> True
//       | Some last_i -> last_i.idn <> idn
//       )
//     )
// let lemma1 tr p sid idn full_st i sid_i init_i last_i tr1 tr2 =
//   get_state_aux_same p sid_i tr1 tr2;
//   let (Some state_i, _) =  get_state p sid_i tr2 in
//   assert(state_i = last_i );
//   let (Some state_i_before_old, _) = get_state p sid_i tr1 in
//   assert(state_i_before_old = state_i);
//   admit();
//   // match get_full_state p tr_before_old with
//   // | None -> admit()
//   // | Some full_state_before_old -> (
//   // get_state_appears_in_full_state tr_before_old p sid_i;
//   // assert(exists (j:nat{j < List.length full_state_before_old}) init. List.index full_state_before_old j = (sid_i, Snoc init state_i_before_old));
//   // admit();
//   // // assert(global_state_pred tr_before_old p sid oldst_b);
//   ()
//  // )

val append_to_non_empty:
  #a:eqtype -> #b:eqtype -> key:a -> elem:b ->
  Lemma (forall xys. [] <> append_to xys key elem)
let append_to_non_empty key elem = ()


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

let suffix_at_event (tr:trace) (ev:trace_event{event_exists tr ev}) =
  let tr_before = tr `prefix_before_event` ev in
  tr `suffix_after` tr_before

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



let suffix_at_event_is_suffix (tr:trace) (ev:trace_event{event_exists tr ev}) :
  Lemma
  (
   tr `has_suffix` (tr `suffix_at_event` ev) 
  )
  = () //suffix_after_is_suffix tr ( tr `prefix_before_event` ev )

let grows_nil (tr:trace):
  Lemma (Nil <$ tr)
  [SMTPat (Nil <$ tr)]
  = 
  reveal_opaque (`%grows) grows 

let rec suffix_after_nil (tr:trace):
  Lemma 
  ( tr `suffix_after` Nil = tr
  )
  [SMTPat (tr `suffix_after` Nil)]
  = match tr with
  | Nil -> ()
  | Snoc init ev -> 
         suffix_after_nil init

let rec suffix_at_event_same_for_suffix (tr:trace) (suff:trace) (the_ev:trace_event):
  Lemma
  (requires 
    tr `has_suffix` suff
    /\ event_exists tr the_ev /\ event_exists suff the_ev
  )
  (ensures 
    tr `suffix_at_event` the_ev = suff `suffix_at_event` the_ev
  )
=
  let tr_before = tr `prefix_before_event` the_ev in
  let suff_before = suff `prefix_before_event` the_ev in
  match suff with
  | Nil -> ()
  | Snoc suff_init suff_ev ->
         match tr with
         | Nil -> ()
         | Snoc tr_init tr_ev -> 
                if tr_ev = the_ev
                then ()
                else suffix_at_event_same_for_suffix tr_init suff_init the_ev

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
  = admit()

#push-options "--z3rlimit 25 " // --z3cliopt 'smt.qi.eager_threshold=50'"
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
                             let tr_after_last_i = (tr `suffix_after_event` (SetState p sid_i last_i_b) ) in
                             let tr_after_oldst = tr `suffix_after_event` (SetState p sid oldst_b) in
                             if tr_after_oldst `has_suffix` tr_after_last_i // last_i after oldst on tr
                             then (
                               get_state_no_set_state_for_on_suffix_after_event tr p sid;
                               no_set_state_entry_for_on_suffix tr_after_oldst tr_after_last_i p sid;
                               assert(no_set_state_entry_for p sid tr_after_last_i);
                               let tr_before_last_i = tr `prefix_before_event` (SetState p sid_i last_i_b) in
                               assume(tr `suffix_after` tr_before_last_i = (Snoc Nil (SetState p sid_i last_i_b)) `trace_concat` tr_after_last_i );
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
                             else ( // oldst before last_i on tr
                               suffixes tr tr_after_last_i tr_after_oldst;
                               assert(tr_after_last_i `has_suffix` tr_after_oldst);
  
                               let oldst_entry = SetState p sid oldst_b in
                               let tr_before_old = tr `prefix_before_event` oldst_entry in
                               let tr_suff_at_old = tr `suffix_at_event` oldst_entry in
                               assume(tr_after_last_i `has_suffix` tr_suff_at_old );
                               get_state_no_set_state_for_on_suffix_after_event tr p sid_i;
                               no_set_state_entry_for_on_suffix tr_after_last_i tr_suff_at_old p sid_i;
                               assert(no_set_state_entry_for p sid_i tr_suff_at_old);
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
