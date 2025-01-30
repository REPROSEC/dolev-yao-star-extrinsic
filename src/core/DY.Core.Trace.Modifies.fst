module DY.Core.Trace.Modifies

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.Manipulation
open DY.Core.Trace.Arithmetic
open DY.Core.Trace.Arithmetic.Derived
open DY.Core.Bytes.Type
open DY.Core.Label.Type

open FStar.Set

type address = principal & state_id

type modifies_set = set address

/// Set lemmas

val lemma_union_empty :
  #a:eqtype -> s:set a ->
  Lemma (union s empty == s /\ union empty s == s)
  [SMTPatOr [
    [SMTPat (union s empty)];
    [SMTPat (union empty s)]
  ]]
let lemma_union_empty s =
  assert(equal (union s empty) s);
  assert(equal (union empty s) s)

/// Modifies functions

val trace_modifies :
  #label_t:Type -> trace_ label_t ->
  modifies_set
let rec trace_modifies tr =
  match tr with
  | Nil -> Set.empty
  | Snoc hd (SetState p sid _) -> Set.add (p, sid) (trace_modifies hd)
  | Snoc hd _ -> trace_modifies hd

val trace_modifies_spec :
  #label_t:Type -> tr:trace_ label_t -> prin:principal -> sid:state_id ->
  Lemma ((prin, sid) `mem` (trace_modifies tr) <==> exists b. state_was_set tr prin sid b)
let rec trace_modifies_spec tr prin sid =
  match tr with
  | Nil -> ()
  | Snoc hd (SetState prin' sid' b) -> begin
    if prin' = prin && sid' = sid then ()
    else trace_modifies_spec hd prin sid
  end
  | Snoc hd _ -> trace_modifies_spec hd prin sid

val trace_modifies_concat  :
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma (trace_modifies (tr1 <++> tr2) == union (trace_modifies tr1) (trace_modifies tr2))
  [SMTPat (trace_modifies (tr1 <++> tr2))]
let rec trace_modifies_concat tr1 tr2 =
  if is_empty tr2 then trace_concat_empty_trace tr1
  else begin
    trace_modifies_concat tr1 (init tr2);
    trace_concat_append_entry tr1 (init tr2) (last tr2);
    // triggers lemma_equal_elim and lemma_equal_intro
    assert(equal (trace_modifies (tr1 <++> tr2)) (union (trace_modifies tr1) (trace_modifies tr2)))
  end

val traceful_modifies :
  #a:Type -> traceful a -> trace ->
  modifies_set
let traceful_modifies f tr_in =
  let (_, tr_out) = f tr_in in
  trace_modifies (tr_out <--> tr_in)


/// Lemmas to automate modifies analysis

val traceful_modifies_bind :
  #a:Type -> #b:Type ->
  x:traceful a -> f:(a -> traceful b) ->
  tr_in:trace ->
  Lemma
  (ensures (
    let (y, tr_mid) = x tr_in in
    traceful_modifies ((let*) x f) tr_in ==
    union (traceful_modifies x tr_in) (traceful_modifies (f y) tr_mid)
  ))
  [SMTPat (traceful_modifies ((let*) x f) tr_in)]
let traceful_modifies_bind x f tr_in =
  let (y, tr_mid) = x tr_in in
  let (_, tr_out) = f y tr_mid in
  // Triggers trace_subtract_concat_slices
  assert(((tr_mid <--> tr_in) <++> (tr_out <--> tr_mid)) == (tr_out <--> tr_in))

val traceful_modifies_return :
  #a:Type ->
  x:a -> tr:trace ->
  Lemma (traceful_modifies (return x) tr == empty)
  [SMTPat (traceful_modifies (return x) tr)]
let traceful_modifies_return x tr = ()

val traceful_modifies_get_trace :
  tr:trace ->
  Lemma (traceful_modifies get_trace tr == empty)
  [SMTPat (traceful_modifies get_trace tr)]
let traceful_modifies_get_trace tr = ()

val traceful_modifies_guard_tr :
  b:bool -> tr:trace ->
  Lemma (traceful_modifies (guard_tr b) tr == empty)
  [SMTPat (traceful_modifies (guard_tr b) tr)]
let traceful_modifies_guard_tr b tr = ()

val traceful_modifies_add_entry :
  e:trace_entry ->
  tr:trace ->
  Lemma
  (ensures (
    traceful_modifies (add_entry e) tr == (match e with
    | SetState prin sid _ -> singleton (prin, sid)
    | _ -> empty
    )
  ))
  [SMTPat (traceful_modifies (add_entry e) tr)]
let traceful_modifies_add_entry e tr =
  /// TODO Can we find a way to remove the need for these next two lines?
  let (_, tr_out) = add_entry e tr in
  assert(tr_out == append_entry tr e);
  match e with
  | SetState prin sid _ -> assert(equal (add (prin, sid) empty) (singleton (prin, sid)))
  | _ -> ()

val traceful_modifies_get_time :
  tr:trace ->
  Lemma (traceful_modifies get_time tr == empty)
  [SMTPat (traceful_modifies get_time tr)]
let traceful_modifies_get_time tr = ()

val traceful_modifies_send_msg :
  b:bytes -> tr:trace ->
  Lemma (traceful_modifies (send_msg b) tr == empty)
  [SMTPat (traceful_modifies (send_msg b) tr)]
let traceful_modifies_send_msg b tr =
  reveal_opaque (`%send_msg) (send_msg)

val traceful_modifies_recv_msg :
  ts:timestamp -> tr:trace ->
  Lemma (traceful_modifies (recv_msg ts) tr == empty)
  [SMTPat (traceful_modifies (recv_msg ts) tr)]
let traceful_modifies_recv_msg ts tr = ()

val traceful_modifies_mk_rand :
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma (traceful_modifies (mk_rand usg lab len) tr == empty)
  [SMTPat (traceful_modifies (mk_rand usg lab len) tr)]
let traceful_modifies_mk_rand usg lab len tr =
  reveal_opaque (`%mk_rand) (mk_rand)

val traceful_modifies_set_state :
  prin:principal -> sid:state_id -> b:bytes -> tr:trace ->
  Lemma (traceful_modifies (set_state prin sid b) tr == singleton (prin, sid))
  [SMTPat (traceful_modifies (set_state prin sid b) tr)]
let traceful_modifies_set_state prin sid b tr =
  reveal_opaque (`%set_state) (set_state)

val traceful_modifies_new_session_id :
  prin:principal -> tr:trace ->
  Lemma (traceful_modifies (new_session_id prin) tr == empty)
  [SMTPat (traceful_modifies (new_session_id prin) tr)]
let traceful_modifies_new_session_id prin tr = ()

val traceful_modifies_get_state :
  prin:principal -> sid:state_id -> tr:trace ->
  Lemma (traceful_modifies (get_state prin sid) tr == empty)
  [SMTPat (traceful_modifies (get_state prin sid) tr)]
let traceful_modifies_get_state prin sid tr = ()

val traceful_modifies_trigger_event :
  prin:principal -> tag:string -> b:bytes -> tr:trace ->
  Lemma (traceful_modifies (trigger_event prin tag b) tr == empty)
  [SMTPat (traceful_modifies (trigger_event prin tag b) tr)]
let traceful_modifies_trigger_event prin tag b tr =
  reveal_opaque (`%trigger_event) (trigger_event)

/// The core properties --- if a trace (or traceful function) does not modify a given address,
/// the result of looking up the state at the start and end of that trace (traceful) is the same.

val trace_concat_same_state_aux :
  prin:principal -> sid:state_id ->
  tr1:trace -> tr2:trace ->
  Lemma
  (requires ~((prin, sid) `mem` (trace_modifies tr2)))
  (ensures get_state_aux prin sid tr1 == get_state_aux prin sid (tr1 <++> tr2))
let trace_concat_same_state_aux prin sid tr1 tr2 =
  let is_state_for prin sess_id e =
    match e with
    | SetState prin' sess_id' content -> prin = prin' && sess_id = sess_id'
    | _ -> false
  in
  trace_modifies_spec tr2 prin sid;
  introduce forall ts. ts `on_trace` tr2 ==> (~(is_state_for prin sid (get_entry_at tr2 ts)))
  with introduce _ ==> _
  with _. begin
    match get_entry_at tr2 ts with
    | SetState prin' sid' b -> ()
    | _ -> ()
  end;
  trace_search_last_concat tr1 tr2 (is_state_for prin sid);
  match trace_search_last tr1 (is_state_for prin sid) with
  | None -> ()
  | Some ts -> trace_concat_get_entry tr1 tr2 ts

val trace_grows_same_state_aux :
  prin:principal -> sid:state_id ->
  tr1:trace -> tr2:trace ->
  Lemma
  (requires tr1 <$ tr2 /\ ~((prin, sid) `mem` (trace_modifies (tr2 <--> tr1))))
  (ensures (get_state_aux prin sid tr1) == (get_state_aux prin sid tr2))
let trace_grows_same_state_aux prin sid tr1 tr2 =
  trace_concat_same_state_aux prin sid tr1 (tr2 <--> tr1)

val traceful_unmodified_same_state_aux:
  #a:Type ->
  prin:principal -> sid:state_id ->
  f:traceful a ->
  tr_in:trace ->
  Lemma
  (requires ~((prin, sid) `mem` (traceful_modifies f tr_in)))
  (ensures (
    let (_, tr_out) = f tr_in in
    get_state_aux prin sid tr_in == get_state_aux prin sid tr_out
  ))
let traceful_unmodified_same_state_aux prin sid f tr_in =
  let (_, tr_out) = f tr_in in
  trace_grows_same_state_aux prin sid tr_in tr_out


let trace_concat_same_state (prin:principal) (sid:state_id) (tr1 tr2:trace)
  : Lemma
    (requires ~((prin, sid) `mem` (trace_modifies tr2)))
    (ensures (
      let (st_opt1, _) = get_state prin sid tr1 in
      let (st_opt2, _) = get_state prin sid (tr1 <++> tr2) in
      st_opt1 == st_opt2
    ))
  = reveal_opaque (`%get_state) (get_state);
    trace_concat_same_state_aux prin sid tr1 tr2

let trace_grows_same_state (prin:principal) (sid:state_id) (tr1 tr2:trace)
  : Lemma
    (requires tr1 <$ tr2 /\ ~((prin, sid) `mem` (trace_modifies (tr2 <--> tr1))))
    (ensures (
      let (st_opt1, _) = get_state prin sid tr1 in
      let (st_opt2, _) = get_state prin sid tr2 in
      st_opt1 == st_opt2
    ))
    [SMTPat (get_state prin sid tr1);
     SMTPat (get_state prin sid tr2);
     SMTPat (~((prin, sid) `mem` (trace_modifies (tr2 <--> tr1))));
    ]
  = trace_concat_same_state prin sid tr1 (tr2 <--> tr1)

let traceful_unmodified_same_state (#a:Type) (prin:principal) (sid:state_id) (f:traceful a) (tr:trace)
  : Lemma
    (requires ~((prin, sid) `mem` (traceful_modifies f tr)))
    (ensures (
      let (st_opt1, _) = get_state prin sid tr in
      let (_, tr_out) = f tr in
      let (st_opt2, _) = get_state prin sid tr_out in
      st_opt1 == st_opt2
    ))
  = let (_, tr_out) = f tr in
    assert(~((prin, sid) `mem` (trace_modifies (tr_out <--> tr))));
    ()

/// TODO: Some simple testing of the analysis
/// Should we put this in an example file? Remove it? Add some kind of test suite?

let unmodified_test (prin:principal) (sid:state_id)
  : traceful (option bytes & option bytes)
  = let* st_opt1 = get_state prin sid in
    let* new_rand = mk_rand NoUsage (DY.Core.Label.principal_label prin) 32 in
    let* msg_ts = send_msg new_rand in
    trigger_event prin "test_event" (Literal (Seq.Base.empty));*
    let* _ = recv_msg msg_ts in
    let* st_opt2 = get_state prin sid in
    return (st_opt1, st_opt2)

#push-options "--z3rlimit 100"
let unmodified_test_proof (prin:principal) (sid:state_id) (tr_in:trace)
  : Lemma
    (let ((st_opt1, st_opt2), _) = unmodified_test prin sid tr_in in
     st_opt1 == st_opt2
    )
  = assert(traceful_modifies (unmodified_test prin sid) tr_in == empty);
    traceful_unmodified_same_state_aux prin sid (unmodified_test prin sid) tr_in;
    ()
#pop-options
