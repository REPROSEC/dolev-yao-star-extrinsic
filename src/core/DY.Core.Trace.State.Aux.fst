module DY.Core.Trace.State.Aux

open DY.Core.Trace.Type
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type

type state_raw = bytes
type session_raw = rev_list state_raw
type full_state_raw = list (state_id * session_raw) 
//TODO: this should be `Map state_id session_raw`, can we extract the generic Map part from DY.Lib.State.Map?
// or is it not worth the effort?

val max: int -> int -> int
let max x y =
  if x < y then y else x

/// To add a new session to a state of a principal,
/// we have to find a new identifier
/// that is not used in the current state of the principal.

val compute_new_session_id: principal -> trace -> state_id
let rec compute_new_session_id prin tr =
  match tr with
  | Nil -> {the_id = 0}
  | Snoc tr_init evt -> (
    match evt with
    | SetState prin' sess_id _ ->
      if prin = prin' then
        {the_id = 
             max (sess_id.the_id + 1) (compute_new_session_id prin tr_init).the_id}
      else
        compute_new_session_id prin tr_init
    | _ -> compute_new_session_id prin tr_init
  )

// Sanity check
val compute_new_session_id_correct:
  prin:principal -> tr:trace ->
  sess_id:state_id -> state_content:bytes ->
  Lemma
  (requires event_exists tr (SetState prin sess_id state_content))
  (ensures sess_id.the_id < (compute_new_session_id prin tr).the_id)
let rec compute_new_session_id_correct prin tr sess_id state_content =
  match tr with
  | Nil -> ()
  | Snoc tr_init evt -> (
    if evt = SetState prin sess_id state_content then ()
    else (
      compute_new_session_id_correct prin tr_init sess_id state_content
    )
  )

val get_state_aux: principal -> state_id -> trace -> option state_raw
let rec get_state_aux prin sess_id tr =
  match tr with
  | Nil -> None
  | Snoc tr_init (SetState prin' sess_id' content) -> (
    if prin = prin' && sess_id = sess_id' then
      Some content
    else
      get_state_aux prin sess_id tr_init
  )
  | Snoc tr_init _ ->
      get_state_aux prin sess_id tr_init

val get_session_aux: principal -> state_id -> trace -> session_raw
let rec get_session_aux prin sess_id tr = 
  match tr with
  | Nil -> Nil
  | Snoc init (SetState p' sid' content) ->
      if p' = prin && sid' = sess_id
        then Snoc (get_session_aux prin sess_id init) content
        else (get_session_aux prin sess_id init)
  | Snoc init _ -> (get_session_aux prin sess_id init)

val get_session: principal -> state_id -> trace -> option session_raw
let get_session prin sess_id tr =
  match get_session_aux prin sess_id tr with
  | Nil -> None
  | sess -> Some sess
  
let _ =
  let p = "a" in
  let sid = {the_id = 1} in
  let b = Literal (FStar.Seq.Base.empty) in
  let tr = Snoc (Snoc Nil (SetState p sid b)) (SetState p sid b) in
  assert(get_session p sid tr = Some (Snoc (Snoc Nil b) b));
  assert(None? (get_session "b" sid tr))

val append_to: #a:eqtype -> #b:Type -> list (a * rev_list b) -> a -> b -> list (a * rev_list b)
let append_to xys key elem =
  let (key_elems,rest) = FStar.List.Tot.Base.partition (fun (x, _) -> x = key) xys in
  let new_key_elems = 
    match key_elems with
    | [] -> Snoc Nil elem
    | Cons (k,elems) _ -> Snoc elems elem
    in
  (key, new_key_elems) :: rest // re-ordering shouldn't matter, since key is included

let _ = 
  let xs = [(1, Snoc Nil 5); (5, Nil)] in
  assert(append_to xs 5 7 = [(5, Snoc Nil 7); (1, Snoc Nil 5)])

val get_full_state_aux: principal -> trace -> full_state_raw -> full_state_raw
let rec get_full_state_aux prin tr curr_state =
  match tr with
  | Nil -> curr_state
  | Snoc init (SetState p' sid' content) ->
      if p' = prin 
        then begin
          let new_state = append_to curr_state sid' content in
          get_full_state_aux prin init new_state
        end
        else get_full_state_aux prin init curr_state
  | Snoc init _ -> get_full_state_aux prin init curr_state

val get_full_state: principal -> trace -> option full_state_raw
let get_full_state prin tr = 
  let next_state_id = compute_new_session_id prin tr in
  if next_state_id.the_id = 0
    then None
    else begin
      let full_state_init = [] in
      match get_full_state_aux prin tr full_state_init with
      | [] -> None
      | fst -> Some fst
    end

let _ =
  let p = "a" in
  let sid1 = {the_id = 1} in
  let sid2 = {the_id = 2} in
  let b = Literal (FStar.Seq.Base.empty) in
  let tr = Snoc (Snoc Nil (SetState p sid1 b)) (SetState p sid2 b) in
  assert(get_full_state p tr = Some [(sid1, (Snoc Nil b)); (sid2, Snoc Nil b)]);
  assert(None? (get_full_state "b" tr))
