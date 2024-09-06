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
// (See Identifier.General for a first try)
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
  
