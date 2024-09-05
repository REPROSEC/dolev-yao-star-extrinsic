module DY.Example.Invariants.Uniqueness.Identifier

open Comparse
open DY.Core
module L = DY.Lib

#set-options "--fuel 1 --ifuel 1"

(*** A class for identifiers stored in states ***)
/// all of this is very similar to [compute_new_session_id]

type session_t #state_t = sess:rev_list state_t{Snoc? sess}
type full_state_t #state_t = list (state_id * session_t #state_t)

// For now, identifiers are nats.
// The idea is, that we maybe want to use other things as identifiers as well
// (for example, randomly generated nonces)
// If we have appropriate functions and properties to define identifiers,
// we can make the rest more general.
// (Ideas so far:
//  * we need a generating function [compute_new]
//  * the overall property should be [new_idn_does_not_appear_in_full_state]
//      * what properties of the generating function do we need for that?
// )
type identifier = nat

class has_identifier (state_t:Type) = {
  base: parseable_serializeable bytes state_t;
  to_id: state_t -> identifier;
}



(*** Generating a new Identifier ***)

let rec find_max_id_in_session_ (#state_t:Type) {|hid: has_identifier state_t |} 
    (sess:rev_list state_raw) : identifier = 
    match sess with
    | Nil -> 0
    | Snoc rest state -> 
        match parse state_t #hid.base state with
        | None -> find_max_id_in_session_ #state_t rest
        | Some st ->
        max (to_id st) (find_max_id_in_session_ #state_t rest)

let find_max_id_in_session (#state_t:Type) {|hid: has_identifier state_t |} 
    (sess:session_raw) : identifier =
    find_max_id_in_session_ #state_t sess

let rec find_max_id_in_full_state (#state_t:Type) {|hid: has_identifier state_t|}  
  (st:full_state_raw): identifier = 
    match st with
    | [] -> 0
    | (_,sess)::rest -> 
        max (find_max_id_in_session #state_t sess) (find_max_id_in_full_state #state_t rest)

val compute_new_id: (#state_t:Type) -> {|hid: has_identifier state_t|} -> principal -> traceful identifier
let compute_new_id #state_t #hid prin =
  let* opt_fst = get_full_state prin in
  match opt_fst with
  | None -> return (1 <: nat)
  | Some fst -> 
        return ((find_max_id_in_full_state #state_t fst + 1)<:nat)

(*** Showing that a newly generated identifier is indeed unique ***)

(** Stating Properties **)

let prop_state_on (#a:Type) (#state_t:Type) {|ps_state : parseable_serializeable bytes state_t|} 
  (from_state: state_t  -> a) (p: a -> bool ) (state:state_raw) : prop =
  match parse state_t state with
  | None -> True
  | Some state -> p (from_state state)


let forall_ids  (#state_t:Type) {|hid:has_identifier state_t|}  
   (sess:(session_raw)) (p: identifier -> bool) : prop =
  forall_rev_list sess (fun state -> prop_state_on #_ #state_t #hid.base to_id p state )


let id_does_not_appear_in_session (#state_t:Type) {|has_identifier state_t|}  
  (id:identifier) (sess:session_raw)  : prop =
  forall_ids #state_t sess (fun id' -> id <> id')


let forall_sessions_ (#state_t:Type) (fst:full_state_t) (p:state_id -> session_t #state_t ->  prop)  : prop =
  forall sid sess. (sid, sess) `List.memP` fst ==> p sid sess


let idn_does_not_appear_in_full_state (#state_t:Type) {|has_identifier state_t|}  
  (id:identifier) (fst:full_state_raw) : prop =
  forall_sessions fst 
    (fun _ sess -> id `id_does_not_appear_in_session #state_t` sess)


(** Proofs **)


let forall_rev_list_singleton (#a:Type) (x: a) (p: a -> prop):
  Lemma
  (forall_rev_list (Snoc Nil x) p <==> p x
  )
  [SMTPat (forall_rev_list (Snoc Nil x) p)]
  = normalize_term_spec (memP #a)
  
val max_id_in_session_largest:
  (#state_t:Type) -> {| hid: has_identifier state_t|} ->
  sess:session_raw ->
  Lemma 
  ( let m_idn = find_max_id_in_session #_ #hid sess in
    forall_ids #state_t sess (fun idn -> m_idn >= idn)
  )
let rec max_id_in_session_largest #state_t #hid sess = 
  let m_idn = find_max_id_in_session #state_t sess in
  match sess with
  | Snoc Nil state -> (
      match parse state_t #hid.base state with
      | None -> ()
      | Some st -> ()
  )
  | Snoc rest state ->
      max_id_in_session_largest #state_t #hid rest


val curr_max_id_largest :
(#state_t:Type) -> {|has_identifier state_t|}  ->
  (to_id: (state_t -> identifier)) ->
  fst: full_state_raw -> 
  Lemma 
  ( let c_max = find_max_id_in_full_state #state_t fst in
    forall_sessions fst (fun sid sess -> forall_ids #state_t sess  (fun idn -> c_max >= idn))
  )
let rec curr_max_id_largest #state_t to_id fst =
  let c_max = find_max_id_in_full_state #state_t fst in
  match fst with
  | [] -> ()
  | (_, sess) :: rest ->
        max_id_in_session_largest #state_t sess;
        curr_max_id_largest to_id rest

/// The Main Property
val new_idn_does_not_appear_in_full_state:
(#state_t:Type) -> {|hid:has_identifier state_t|}  ->
p:principal -> tr:trace ->
  Lemma
  (requires has_full_state_for tr p
  )
  (ensures (
    let (n_id,_) = compute_new_id #state_t p tr in
    let fst = access_full_state tr p in
    n_id `idn_does_not_appear_in_full_state #state_t` fst
  ))
let new_idn_does_not_appear_in_full_state #state_t #hid p tr =
  let fst = access_full_state tr p in
  curr_max_id_largest #state_t to_id fst
  
(*** More general  ***)

open PreOrd

class identifier_ (id_t:eqtype) {|ord_leq id_t|} = {
  initial_id: id_t;
  next_id: id_t -> id_t;
  next_id_larger: x:id_t -> Lemma (x `lt` next_id x)
}

// the main property: new_identifier > current max identifier
class has_identifier_ (state_t:Type) (id_t:eqtype) {|ord_leq id_t|} {|identifier_ id_t|} = {
  base_: parseable_serializeable bytes state_t;
  to_id_: state_t -> id_t;
}

// returns Some only for sessions where all states can be successfully parsed
let rec find_max_id_in_session_gen (#state_t:Type) (#id_t:eqtype) {|ord_leq id_t |} {|identifier_ id_t|} {|hid: has_identifier_ state_t id_t|} 
    (sess:rev_list state_raw) 
    : option id_t = 
    match sess with
    | Nil -> None
    | Snoc rest state -> 
        match parse state_t #hid.base_ state with
        | None -> find_max_id_in_session_gen #state_t #_ #_ #_ #hid rest
        | Some st -> (
            match find_max_id_in_session_gen #state_t #_ #_ #_ #hid rest with
            | None -> Some (to_id_ st)
            | Some cur_max ->
         Some (max (hid.to_id_ st) cur_max)
        )


// let prop_state_on (#a:Type) (#state_t:Type) {|ps_state : parseable_serializeable bytes state_t|} 
//   (from_state: state_t  -> a) (p: a -> bool ) (state:state_raw) : prop =
//   match parse state_t state with
//   | None -> True
//   | Some state -> p (from_state state)

let forall_ids_gen  (#state_t:Type) (#id_t:eqtype) {|ord_leq id_t|} {|identifier_ id_t|} {|hid:has_identifier_ state_t id_t|}  
   (sess:(session_raw)) (p: id_t -> bool) : prop =
  forall_rev_list sess (fun state -> prop_state_on #_ #state_t #hid.base_ hid.to_id_ p state )


let rec find_max_id_in_session_gen_none
(#state_t:Type) (#id_t:eqtype) {|ord_leq id_t |} {|identifier_ id_t|} {|hid: has_identifier_ state_t id_t|} 
    (sess:rev_list state_raw) 
    : Lemma 
    (requires None? (find_max_id_in_session_gen #state_t #id_t sess))
    (ensures
       forall_rev_list sess (fun st -> None? (parse state_t #hid.base_ st))
    )
= match sess with
  | Nil -> ()
  | Snoc rest st -> find_max_id_in_session_gen_none #state_t #id_t rest


#push-options "--fuel 4 --ifuel 4"
val max_id_in_session_largest_gen:
  (#state_t:Type) -> (#id_t:eqtype) -> {|ord_leq id_t |} -> {|identifier_ id_t|} -> {| hid: has_identifier_ state_t id_t|} ->
  sess:session_raw ->
  Lemma 
  ( let m_idn = find_max_id_in_session_gen #_ #_ #_ #_ #hid sess in
    match m_idn with
    | Some m_idn ->
    forall_ids_gen #state_t sess (fun idn -> idn `leq` m_idn)
    | None -> True
  )
let rec max_id_in_session_largest_gen #state_t #id_t #_ #_ #hid sess = 
  let m_idn = find_max_id_in_session_gen #state_t #id_t sess in
  match m_idn with
  | None -> ()
  | Some m_idn -> (
  match sess with
  | Snoc Nil state -> ()
  | Snoc rest state -> 
  max_id_in_session_largest_gen #state_t #id_t rest;
      match parse state_t #hid.base_ state with
      | None -> ()
      | Some st ->
      match find_max_id_in_session_gen #state_t #id_t rest with
      | None -> ( find_max_id_in_session_gen_none #state_t #id_t rest
)
      | Some m_idn_rest -> (
       max_is_largest (hid.to_id_ st) m_idn_rest
))


let rec find_max_id_in_full_state_gen (#state_t:Type) (#id_t:eqtype) {|ord_leq id_t|} {|identifier_ id_t|} {|hid: has_identifier_ state_t id_t|}  
  (st:full_state_raw): option id_t = 
    match st with
    | [] -> None
    | (_,sess)::rest ->
        match (find_max_id_in_session_gen #state_t #id_t sess) with
        | None -> (find_max_id_in_full_state_gen #state_t rest)
        | Some sess_max_id -> 
        match (find_max_id_in_full_state_gen #state_t rest) with
        | None -> Some sess_max_id
        | Some rest_max_id ->
        Some (max sess_max_id rest_max_id)

val compute_new_id_gen: (#state_t:Type) -> (#id_t:eqtype) -> {|ord_leq id_t|} -> {|identifier_ id_t|} -> {|hid: has_identifier_ state_t id_t|} -> principal -> traceful id_t
let compute_new_id_gen #state_t #id_t #_ #hid prin =
  let* opt_fst = get_full_state prin in
  match opt_fst with
  | None -> return (hid.initial_id)
  | Some fst ->
      match (find_max_id_in_full_state_gen #state_t #id_t fst) with
      | None -> return hid.initial_id
      | Some cur_max ->
        return (
        hid.next_id cur_max)



let rec find_max_id_in_full_state_gen_none
(#state_t:Type) (#id_t:eqtype) {|ord_leq id_t|} {|identifier_ id_t|} {|hid: has_identifier_ state_t id_t|}  
  (f_st:full_state_raw):
  Lemma
  (requires None? (find_max_id_in_full_state_gen #state_t #id_t f_st))
  (ensures
     forall_sessions f_st 
       (fun sid sess ->
         forall_rev_list sess (fun st -> None? (parse state_t #hid.base_ st))
       )
  )
  = match f_st with
  | [] -> ()
  | (sid,sess)::rest ->
                    find_max_id_in_session_gen_none #state_t #id_t sess;
                    find_max_id_in_full_state_gen_none #state_t #id_t rest

#push-options "--z3rlimit 20"
val curr_max_id_largest_gen :
(#state_t:Type) -> (#id_t:eqtype) -> {|ord_leq id_t |} -> {|identifier_ id_t|} -> {|hid:has_identifier_ state_t id_t|}  ->
  (to_id: (state_t -> id_t)) ->
  fst: full_state_raw -> 
  Lemma 
  ( //let c_max = find_max_id_in_full_state_gen #state_t fst in
   match find_max_id_in_full_state_gen #state_t fst with
   | None -> True
   | Some c_max ->
    forall_sessions fst (fun sid sess -> forall_ids_gen #state_t #id_t sess  (fun idn -> idn `leq` c_max))
  )
let rec curr_max_id_largest_gen #state_t #id_t #_ #hid to_id fst =
  match find_max_id_in_full_state_gen #state_t #id_t fst with 
  | None -> ()
  | Some c_max ->
  match fst with
  | [] -> ()
  | (sid, sess) :: rest ->
        max_id_in_session_largest_gen #state_t #id_t sess;
        curr_max_id_largest_gen #state_t #id_t to_id rest;
        match (find_max_id_in_session_gen #state_t #id_t sess) with
        | None -> find_max_id_in_session_gen_none #state_t #id_t sess
        | Some sess_max_id -> (
            match (find_max_id_in_full_state_gen #state_t rest) with
            | None -> 
                find_max_id_in_full_state_gen_none #state_t #id_t rest
            | Some rest_max_id -> (
                max_is_largest sess_max_id rest_max_id
        )
  )
#pop-options

let id_does_not_appear_in_session_gen (#state_t:Type) (#id_t:eqtype) {|ord_leq id_t|} {|identifier_ id_t|} {|has_identifier_ state_t id_t|}  
  (id:id_t) (sess:session_raw)  : prop =
  forall_ids_gen #state_t #id_t sess (fun id' -> id <> id')


let idn_does_not_appear_in_full_state_gen (#state_t:Type) (#id_t:eqtype) {|ord_leq id_t|} {|identifier_ id_t|} {|has_identifier_ state_t id_t|}  
  (id:id_t) (fst:full_state_raw) : prop =
  forall_sessions fst 
    (fun _ sess -> id `id_does_not_appear_in_session_gen #state_t #id_t` sess)

#push-options "--z3rlimit 30"
/// The Main Property
val new_idn_does_not_appear_in_full_state_gen:
(#state_t:Type) -> (#id_t:eqtype) -> {|ord_leq id_t|} -> {|identifier_ id_t|} -> {|hid:has_identifier_ state_t id_t|}  ->
p:principal -> tr:trace ->
  Lemma
  (requires has_full_state_for tr p
  )
  (ensures (
    let (n_id,_) = compute_new_id_gen #state_t #id_t p tr in
    let fst = access_full_state tr p in
    n_id `idn_does_not_appear_in_full_state_gen #state_t` fst
  ))
let new_idn_does_not_appear_in_full_state_gen #state_t #id_t #_ #_ #hid p tr =
  let f_st = access_full_state tr p in
  let (n_id,_) = compute_new_id_gen #state_t #id_t p tr in
  curr_max_id_largest_gen #state_t #id_t hid.to_id_ f_st;
  match find_max_id_in_full_state_gen #state_t #id_t f_st with
  | None ->
      find_max_id_in_full_state_gen_none #state_t #id_t f_st
  | Some curr_max -> (
      next_id_larger curr_max
      )
#pop-options


instance identifier_nat: identifier_ nat #ord_leq_nat = {
  initial_id = 1;
  next_id = (fun (i:nat) -> i + 1);
  next_id_larger = (fun i -> ())
}

let rand_bytes = b:bytes{Rand? b}

instance ord_leq_rand_bytes_time: ord_leq rand_bytes = {
  leq_ = (fun (r1 r2:rand_bytes) ->
    let Rand _ _ _ t1 = r1 in
    let Rand _ _ _ t2 = r2 in
    t1 <= t2
  );
  refl = (fun _ -> ());
  total_ = (fun _ _ -> ());
  // anti_symm = (fun _ _ -> ());
  trans = (fun _ _ _ -> ())
  
}

instance identifier_rand (u:usage) (l:label) (len:nat{len <> 0}): identifier_ rand_bytes #ord_leq_rand_bytes_time = {
  initial_id = (Rand u l len 0);
  next_id = (fun (r:rand_bytes) -> 
    let Rand u l len t = r in
    Rand u l len (t+1)
  );
  next_id_larger = (fun r -> ())
}
