module DY.Core.Trace.State.Aux

open FStar.List.Tot

open DY.Core.List
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Trace.PrefixSuffix
open DY.Core.Trace.State.NoSetStateEntry


module List = FStar.List.Tot.Base

/// This module defines helper functions for state handling on traces.
/// The functions will be used in `DY.Core.Trace.Invariant`
/// to define the trace invariant
/// and in `DY.Core.Trace.Maniplation` where some are lifted to the `traceful` monad.


/// Type aliases for the internal state layout
 
type state_raw = bytes
type session_raw = rev_list state_raw // the current state of a session is the last entry
type full_state_raw = list (state_id * session_raw) 
//TODO: full_state_raw should be `Map state_id session_raw`, can we extract the generic Map part from DY.Lib.State.Map?
// or is it not worth the effort?

val max: nat -> nat -> nat
let max x y =
  if x < y then y else x

/// To add a new session to a (full) state of a principal,
/// we have to find a new identifier
/// that is not used in the current state of the principal.

val compute_new_session_id: principal -> trace -> state_id
let rec compute_new_session_id prin tr =
  match tr with
  | Nil -> {the_id = 0}
  | Snoc tr_init (SetState prin' sess_id _) ->
      if prin = prin' then
        {the_id = 
             max (sess_id.the_id + 1) (compute_new_session_id prin tr_init).the_id}
      else
        compute_new_session_id prin tr_init
  | Snoc tr_init _ -> compute_new_session_id prin tr_init
  


(*** Reading state, session, full state from the trace ***)

val get_state_aux: principal -> state_id -> trace -> option state_raw
let rec get_state_aux prin sess_id tr =
  match tr with
  | Nil -> None
  | Snoc tr_init (SetState prin' sess_id' content) -> (
    if prin = prin' && sess_id = sess_id' 
      then Some content
      else get_state_aux prin sess_id tr_init
    )
  | Snoc tr_init _ ->
      get_state_aux prin sess_id tr_init

val get_session_: principal -> state_id -> trace -> session_raw
let rec get_session_ prin sess_id tr = 
  match tr with
  | Nil -> Nil
  | Snoc init (SetState p' sid' content) ->
      if p' = prin && sid' = sess_id
        then Snoc (get_session_ prin sess_id init) content
        else (get_session_ prin sess_id init)
  | Snoc init _ -> (get_session_ prin sess_id init)

val get_session_aux: principal -> state_id -> trace -> option session_raw
let get_session_aux prin sess_id tr =
  match get_session_ prin sess_id tr with
  | Nil -> None
  | sess -> Some sess

// simple tests to show intuition
let _ =
  let p = "a" in
  let sid = {the_id = 1} in
  let b = Literal (FStar.Seq.Base.empty) in
  let tr = Snoc (Snoc Nil (SetState p sid b)) (SetState p sid b) in
  assert(get_session_aux p sid tr = Some (Snoc (Snoc Nil b) b));
  assert(None? (get_session_aux "b" sid tr))


/// Helper function for `get_full_state`

let rec zero_to_sid (sid:state_id) : 
  Tot (list state_id ) 
  (decreases (sid.the_id))
  =
  if sid.the_id = 0
  then [{the_id = 0}]
  else (zero_to_sid {the_id = sid.the_id - 1}) @ [sid]

let get_session_indexed (tr:trace) (prin:principal) (sid:state_id) =
  match get_session prin sid tr with
  | None -> None
  | Some sess -> Some (sid, sess)

// this is not the most efficient way to collect the full state
// (since it goes through the whole trace for every session id)
// but this way makes it easier to prove relations of get_full_state and get_session
// (trys to get the session for every session id 
// smaller than the next (from compute new session)
// collects those ids and session, where session is Some )
val get_full_state: principal -> trace -> option full_state_raw
let get_full_state prin tr = 
  let new_sessid = compute_new_session_id prin tr in
  if new_sessid.the_id = 0
  then None
  else
    Some (List.choose 
      (get_session_indexed tr prin) 
      (zero_to_sid new_sessid)
    )
    
// tests for `get_full_state`
let _ =
  let p = "a" in
  let sid1 = {the_id = 1} in
  let sid2 = {the_id = 2} in
  let b = Literal (FStar.Seq.Base.empty) in
  let b1 = Literal (FStar.Seq.Base.create 1 FStar.UInt8.one ) in
  let tr = Snoc ( Snoc (Snoc Nil (SetState p sid1 b)) (SetState p sid2 b) ) (SetState p sid1 b1) in
  assert(get_session p sid1 tr =  Some (Snoc (Snoc Nil b) b1));
  assert(get_session p sid2 tr = Some (Snoc Nil b));
  
  normalize_term_spec (List.choose #state_id #(state_id* session_raw));
  assert(get_full_state p tr = Some [(sid1, Snoc (Snoc Nil b) b1); (sid2, Snoc Nil b); ]);
  assert(None? (get_full_state "b" tr))





(*** Properties for get_state_aux and get_session_aux ***)

val get_state_aux_state_was_set :
  p:principal -> sid:state_id -> tr:trace ->
  Lemma
    (requires True)
    (ensures (
       match (get_state_aux p sid tr) with
       | None -> True
       | Some v -> state_was_set tr p sid v
      )
    )
    [SMTPat (get_state_aux p sid tr)]
let rec get_state_aux_state_was_set p sid tr =
  match tr with
  | Nil -> ()
  | Snoc init (SetState p' sid' v) ->
     if p' = p && sid' = sid 
       then begin
         let ev = (SetState p' sid' v) in
         assert(event_at tr (DY.Core.Trace.Type.length tr - 1) ev)
       end
       else get_state_aux_state_was_set p sid init
  | Snoc init _ -> get_state_aux_state_was_set p sid init


/// the main property:
/// if there are no more state entries,
/// the last state doesn't change

val get_state_aux_same:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma
    (requires
      tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    )
    (ensures get_state_aux p sid tr1 = get_state_aux p sid tr2)
 //   [SMTPat (tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1))]
let rec get_state_aux_same p sid tr1 tr2 =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);

  if tr1 = tr2 
    then ()
    else begin
       match tr2 with
       | Nil -> ()
       | Snoc init ev -> 
              assert(event_exists (tr2 `suffix_after` tr1) ev);
              suffix_after_for_prefix tr2 init tr1;
              get_state_aux_same p sid tr1 init
    end



/// lifting of the get_state_aux property to get_session_aux

val get_session_aux_same:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma
    (requires
      tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    )
    (ensures get_session_aux p sid tr1 = get_session_aux p sid tr2)
let rec get_session_aux_same p sid tr1 tr2 =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);

  if tr1 = tr2 
    then ()
    else begin
       match tr2 with
       | Nil -> ()
       | Snoc init ev -> 
              assert(event_exists (tr2 `suffix_after` tr1) ev);
              suffix_after_for_prefix tr2 init tr1;
              get_session_aux_same p sid tr1 init
    end
