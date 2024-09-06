module DY.Example.Invariants.Uniqueness.Identifier.General

open Comparse
open DY.Core
module L = DY.Lib
open PreOrd

#set-options "--fuel 1 --ifuel 1"

(*** The identifier class ***)
// any type that is a total preorder can be made an identifier
// by specifying:
// * an initial value (chosen if no prior identifier exists)
// * a function generating the next identifier from the current one
// * showing that the next identifier is strictly larger than the old one
class identifier (id_t:eqtype) {|preord_leq id_t|} = {
  initial_id: id_t;
  next_id: id_t -> id_t;
  next_id_larger: x:id_t -> Lemma (x `lt` next_id x)
}

(** Instances for identifier **)
instance identifier_nat: identifier nat #preord_leq_nat = {
  initial_id = 1;
  next_id = (fun (i:nat) -> i + 1);
  next_id_larger = (fun i -> ())
}

let rand_bytes = refined bytes (Rand?) 
let ps_rand_bytes =
  refine ps_bytes (Rand?) 

instance preord_leq_rand_bytes_time: preord_leq rand_bytes = {
  leq_ = (fun (r1 r2:rand_bytes) ->
    let Rand _ _ _ t1 = r1 in
    let Rand _ _ _ t2 = r2 in
    t1 <= t2
  );
  refl = (fun _ -> ());
  total_ = (fun _ _ -> ());
  trans = (fun _ _ _ -> ())  
}

// this is not really what we want and not working like this
instance identifier_rand (u:usage) (l:label) (len:nat{len <> 0}): identifier rand_bytes #preord_leq_rand_bytes_time = {
  initial_id = (Rand u l len 0);
  next_id = (fun (r:rand_bytes) -> 
    let Rand u l len t = r in
    Rand u l len (t+1)
  );
  next_id_larger = (fun r -> ())
}



(*** The has_identifier class ***)
// read as: "the state type has identifier of type id_t"
// for example, if we have
// type state_t = S: idn:nat -> ctr: nat -> state_t
// we can say that the "idn" field should be an idenfier for the state with:
// instance has_identifier state_t nat = {
//   base = ...
//   to_id = (fun state -> state.idn)
// }
class has_identifier (state_t:Type) (id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} = {
  base: parseable_serializeable bytes state_t;
  to_id: state_t -> id_t;
}

(*** Compute a new identifier ***)
// the idea is:
// * find the current largest identifier (by going through all sessions)
// * generate the next identifier from this current largest one
// * if there is no prior identifier use the initial identifier

let rec find_max_id_in_session  (#state_t:Type) (#id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} {|hid: has_identifier state_t id_t|} 
    (sess:rev_list state_raw) 
    : option id_t = 
    match sess with
    | Nil -> None
    | Snoc rest state -> 
        match parse state_t #hid.base state with
        | None -> find_max_id_in_session #state_t #_ #_ #_ #hid rest
        | Some st ->
            match find_max_id_in_session #state_t #_ #_ #_ #hid rest with
            | None -> Some (to_id st)
            | Some cur_max ->
                Some (max (hid.to_id st) cur_max)

let rec find_max_id_in_full_state (#state_t:Type) (#id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} {|hid: has_identifier state_t id_t|}  
  (st:full_state_raw): option id_t = 
    match st with
    | [] -> None
    | (_,sess)::rest ->
        match (find_max_id_in_session #state_t #id_t sess) with
        | None -> (find_max_id_in_full_state #state_t rest)
        | Some sess_max_id -> 
            match (find_max_id_in_full_state #state_t rest) with
            | None -> Some sess_max_id
            | Some rest_max_id ->
                Some (max sess_max_id rest_max_id)

val compute_new_id: (#state_t:Type) -> (#id_t:eqtype) -> {|preord_leq id_t|} -> {|identifier id_t|} -> {|hid: has_identifier state_t id_t|} -> principal -> traceful id_t
let compute_new_id #state_t #id_t #_ #hid prin =
  let* opt_fst = get_full_state prin in
  match opt_fst with
  | None -> return (hid.initial_id)
  | Some fst ->
      match (find_max_id_in_full_state #state_t #id_t fst) with
      | None -> return hid.initial_id
      | Some cur_max ->
          return (hid.next_id cur_max)


(*** Properties ***)
// the main property is [new_idn_does_not_appear_in_full_state]:
// a newly generated identifier is unique
// first we need some helper lemmas

let prop_state_on (#a:Type) (#state_t:Type) {|ps_state : parseable_serializeable bytes state_t|} 
  (from_state: state_t  -> a) (p: a -> bool ) (state:state_raw) : prop =
  match parse state_t state with
  | None -> True
  | Some state -> p (from_state state)

let rec find_max_id_in_session_none
(#state_t:Type) (#id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} {|hid: has_identifier state_t id_t|} 
    (sess:rev_list state_raw) 
    : Lemma 
    (requires None? (find_max_id_in_session #state_t #id_t sess))
    (ensures
       forall_rev_list sess (fun st -> None? (parse state_t #hid.base st))
    )
= match sess with
  | Nil -> ()
  | Snoc rest st -> find_max_id_in_session_none #state_t #id_t rest


let forall_ids  (#state_t:Type) (#id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} {|hid:has_identifier state_t id_t|}  
   (sess:(session_raw)) (p: id_t -> bool) : prop =
  forall_rev_list sess 
    (fun state -> prop_state_on #_ #state_t #hid.base hid.to_id p state )

#push-options "--fuel 4 --ifuel 4"
val max_id_in_session_largest:
  (#state_t:Type) -> (#id_t:eqtype) -> {|preord_leq id_t|} -> {|identifier id_t|} -> {| hid: has_identifier state_t id_t|} ->
  sess:session_raw ->
  Lemma 
  ( let m_idn = find_max_id_in_session #state_t #id_t #_ #_ #_ sess in
    match m_idn with
    | Some m_idn ->
        forall_ids #state_t sess (fun idn -> idn `leq` m_idn)
    | None -> True
  )
let rec max_id_in_session_largest #state_t #id_t #_ #_ #hid sess = 
  let m_idn = find_max_id_in_session #state_t #id_t sess in
  match m_idn with
  | None -> ()
  | Some m_idn ->
      match sess with
      | Snoc Nil state -> ()
      | Snoc rest state -> 
          max_id_in_session_largest #state_t #id_t rest;
          match parse state_t #hid.base state with
          | None -> ()
          | Some st ->
              match find_max_id_in_session #state_t #id_t rest with
              | None -> find_max_id_in_session_none #state_t #id_t rest
              | Some m_idn_rest ->
               max_is_largest (hid.to_id st) m_idn_rest
#pop-options


let rec find_max_id_in_full_state_none
(#state_t:Type) (#id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} {|hid: has_identifier state_t id_t|}  
  (f_st:full_state_raw):
  Lemma
  (requires None? (find_max_id_in_full_state #state_t #id_t f_st))
  (ensures
     forall_sessions f_st 
       (fun sid sess ->
         forall_rev_list sess (fun st -> None? (parse state_t #hid.base st))
       )
  )
  = match f_st with
  | [] -> ()
  | (sid,sess)::rest ->
      find_max_id_in_session_none #state_t #id_t sess;
      find_max_id_in_full_state_none #state_t #id_t rest

#push-options "--z3rlimit 20"
val max_id_in_full_state_largest :
(#state_t:Type) -> (#id_t:eqtype) -> {|preord_leq id_t|} -> {|identifier id_t|} -> {|hid:has_identifier state_t id_t|}  ->
  (to_id: (state_t -> id_t)) ->
  fst: full_state_raw -> 
  Lemma 
  ( 
   match find_max_id_in_full_state #state_t fst with
   | None -> True
   | Some c_max ->
       forall_sessions fst 
         (fun sid sess -> 
            forall_ids #state_t #id_t sess (fun idn -> idn `leq` c_max))
  )
let rec max_id_in_full_state_largest #state_t #id_t #_ #hid to_id fst =
  match find_max_id_in_full_state #state_t #id_t fst with 
  | None -> ()
  | Some c_max ->
      match fst with
      | [] -> ()
      | (sid, sess) :: rest ->
            max_id_in_session_largest #state_t #id_t sess;
            max_id_in_full_state_largest #state_t #id_t to_id rest;
            match (find_max_id_in_session #state_t #id_t sess) with
            | None -> find_max_id_in_session_none #state_t #id_t sess
            | Some sess_max_id -> (
                match (find_max_id_in_full_state #state_t rest) with
                | None -> 
                    find_max_id_in_full_state_none #state_t #id_t rest
                | Some rest_max_id ->
                    max_is_largest sess_max_id rest_max_id
              )
#pop-options


(*** The main property ***)

let id_does_not_appear_in_session (#state_t:Type) (#id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} {|has_identifier state_t id_t|}  
  (id:id_t) (sess:session_raw)  : prop =
  forall_ids #state_t #id_t sess (fun id' -> id <> id')

let idn_does_not_appear_in_full_state (#state_t:Type) (#id_t:eqtype) {|preord_leq id_t|} {|identifier id_t|} {|has_identifier state_t id_t|}  
  (id:id_t) (fst:full_state_raw) : prop =
  forall_sessions fst 
    (fun _ sess -> id `id_does_not_appear_in_session #state_t #id_t` sess)

#push-options "--z3rlimit 30"
val new_idn_does_not_appear_in_full_state:
(#state_t:Type) -> (#id_t:eqtype) -> {|preord_leq id_t|} -> {|identifier id_t|} -> {|hid:has_identifier state_t id_t|}  ->
p:principal -> tr:trace ->
  Lemma
  (requires has_full_state_for tr p
  )
  (ensures (
    let (n_id,_) = compute_new_id #state_t #id_t p tr in
    let fst = access_full_state tr p in
    n_id `idn_does_not_appear_in_full_state #state_t` fst
  ))
let new_idn_does_not_appear_in_full_state #state_t #id_t #_ #_ #hid p tr =
  let f_st = access_full_state tr p in
  let (n_id,_) = compute_new_id #state_t #id_t p tr in
  max_id_in_full_state_largest #state_t #id_t hid.to_id f_st;
  match find_max_id_in_full_state #state_t #id_t f_st with
  | None ->
      find_max_id_in_full_state_none #state_t #id_t f_st
  | Some curr_max ->
      next_id_larger curr_max
#pop-options



