module DY.Core.Trace.State.Aux

open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Trace.Type

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

val max: int -> int -> int
let max x y =
  if x < y then y else x

/// To add a new session to a (full) state of a principal,
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

(*** Reading state, session, full state from the trace ***)

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

// simple tests to show intuition
let _ =
  let p = "a" in
  let sid = {the_id = 1} in
  let b = Literal (FStar.Seq.Base.empty) in
  let tr = Snoc (Snoc Nil (SetState p sid b)) (SetState p sid b) in
  assert(get_session p sid tr = Some (Snoc (Snoc Nil b) b));
  assert(None? (get_session "b" sid tr))


/// Helper function for `get_full_state`
 
val append_to: #a:eqtype -> #b:Type -> list (a * rev_list b) -> a -> b -> list (a * rev_list b)
let append_to xys key elem =
  let (key_elems,rest) = FStar.List.Tot.Base.partition (fun (x, _) -> x = key) xys in
  let new_key_elems = 
    match key_elems with
    | [] -> Snoc Nil elem
    | Cons (k,elems) _ -> Snoc elems elem
    in
  (key, new_key_elems) :: rest // re-ordering shouldn't matter, since key is attached to elements

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

// tests for `get_full_state`
let _ =
  let p = "a" in
  let sid1 = {the_id = 1} in
  let sid2 = {the_id = 2} in
  let b = Literal (FStar.Seq.Base.empty) in
  let tr = Snoc (Snoc Nil (SetState p sid1 b)) (SetState p sid2 b) in
  assert(get_full_state p tr = Some [(sid1, (Snoc Nil b)); (sid2, Snoc Nil b)]);
  assert(None? (get_full_state "b" tr))


(*** Properties for getter functions ***)


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

val get_state_aux_is_last_of_get_session_aux:
  p:principal -> sid:state_id -> tr:trace ->
  Lemma 
    (requires True
    )
    (ensures (
      let session = get_session_aux p sid tr in
      match get_state_aux p sid tr with
      | None -> Nil? session
      | Some st -> Snoc? session /\ (let Snoc _ last = session in st = last)
    )
    )
let rec get_state_aux_is_last_of_get_session_aux p sid tr = 
  match tr with
  | Nil -> ()
  | Snoc init _ -> get_state_aux_is_last_of_get_session_aux p sid init






/// The main property we want to show is
/// that a particular session of a principal stays the same
/// if there are no more `SetState` entries for this principal and this session on the trace.

/// The property that there are no state entries
/// for the principal and a particular session

val no_set_state_entry_for:
  principal -> state_id -> trace -> prop
let no_set_state_entry_for p sid tr = 
  forall (ts:timestamp{ts < length tr}).
    match get_event_at tr ts with
    | SetState p' sid' _ -> p' <> p \/ sid' <> sid
    | _ -> True

/// if there are no state entries on a trace,
/// this is true for any prefix of the trace.

val no_set_state_entry_for_prefix:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma 
    (requires no_set_state_entry_for p sid tr2 /\ tr1 <$ tr2)
    (ensures no_set_state_entry_for p sid tr1)
    [SMTPat (no_set_state_entry_for p sid tr2); SMTPat (tr1 <$ tr2)]
let no_set_state_entry_for_prefix p sid tr1 tr2 = 
  introduce forall (ts:timestamp{ts < length tr1}). get_event_at tr1 ts = get_event_at tr2 ts
  with begin
    let ev1 = get_event_at tr1 ts in
    event_at_grows tr1 tr2 ts ev1
    end


/// concatenating traces without state entries
/// results in no state entries
#push-options "--fuel 2"
val no_set_state_entry_for_concat:
  p:principal -> sid:state_id ->
  tr1: trace -> tr2:trace ->
  Lemma
    (requires 
        no_set_state_entry_for p sid tr1
      /\ no_set_state_entry_for p sid tr2
    )
    (ensures
      no_set_state_entry_for p sid (tr1 `trace_concat` tr2)
    )
    // [SMTPat (no_set_state_entry_for p sid tr1)
    // ; SMTPat (no_set_state_entry_for p sid tr2)]
let rec no_set_state_entry_for_concat p sid tr1 tr2 =
  match tr2 with
  | Nil -> ()
  | Snoc init2 ev2 -> 
    init_is_prefix tr2;
    assert(event_exists tr2 ev2);
    no_set_state_entry_for_prefix p sid init2 tr2;
    no_set_state_entry_for_concat p sid tr1 init2
#pop-options

/// definition of "trace substraction"
/// (it holds: tr2 = tr1 ++ tr2 `suffix_after` tr1)

val suffix_after: tr2:trace -> tr1:trace{tr1 <$ tr2} -> trace
let rec suffix_after tr2 tr1 = 
  match tr2 with
  | Nil -> Nil
  | Snoc init ev -> 
      if length tr2 = length tr1
        then Nil
        else begin 
             reveal_opaque (`%grows) grows; 
             norm_spec [zeta; delta_only [`%prefix]] (prefix);
             Snoc (suffix_after init tr1) ev
         end

val suffix_after_splits_trace:
  tr2:trace -> tr1:trace{tr1 <$ tr2} ->
  Lemma (tr2 = tr1 `trace_concat` (tr2 `suffix_after` tr1))
let rec suffix_after_splits_trace tr2 tr1 =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr2 with
  | Nil -> ()
  | Snoc init ev -> 
         if length tr1 = length tr2 
           then ()
           else suffix_after_splits_trace init tr1

/// for traces with tr1 <$ tr2 <$ tr3,
/// the suffix after tr1 on tr2
/// is a prefix of
/// the suffix after tr1 on tr3

val suffix_after_for_prefix: 
  tr3:trace -> tr2:trace {tr2 <$ tr3} -> tr1:trace {tr1 <$ tr2} ->
  Lemma 
    (tr2 `suffix_after` tr1 <$ tr3 `suffix_after` tr1)
let rec suffix_after_for_prefix tr3 tr2 tr1 = 
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  if length tr3 = length tr2 || length tr2 = length tr1
    then ()
    else begin
      match tr3 with
      | Nil -> ()
      | Snoc init ev -> suffix_after_for_prefix init tr2 tr1
    end


  
/// for traces with tr1 <$ tr2 <$ tr3,
/// the suffix after tr1 on tr3
/// is the concat of the two pairwise suffixes
#push-options "--fuel 2"
val suffix_after_concat:
  tr1:trace -> tr2:trace {tr1 <$ tr2} -> tr3:trace{tr2 <$ tr3} ->
  Lemma
  ( tr3 `suffix_after` tr1 == (tr2 `suffix_after` tr1) `trace_concat` (tr3 `suffix_after` tr2)
  )
let rec suffix_after_concat tr1 tr2 tr3 =     
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr3 with
  | Nil -> ()
  | Snoc init ev -> 
      if length tr2 = length tr3
        then ()
        else suffix_after_concat tr1 tr2 init
#pop-options

/// transitivity of `no_set_state_entry_for` on suffixes of growing traces
val no_set_state_entry_for_suffixes_transitive:
  p:principal -> sid:state_id ->
  tr1:trace -> tr2:trace{tr1 <$ tr2} -> tr3:trace{tr2 <$ tr3} ->
  Lemma
  (requires
      no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    /\ no_set_state_entry_for p sid (tr3 `suffix_after` tr2)
  )
  (ensures
    no_set_state_entry_for p sid (tr3 `suffix_after` tr1)
  )
let no_set_state_entry_for_suffixes_transitive p sid tr1 tr2 tr3 =
  suffix_after_concat tr1 tr2 tr3;
  no_set_state_entry_for_concat p sid (tr2 `suffix_after` tr1) (tr3 `suffix_after` tr2)

#push-options "--fuel 2"

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
