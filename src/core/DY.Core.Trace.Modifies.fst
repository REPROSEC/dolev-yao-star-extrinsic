module DY.Core.Trace.Modifies

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.Manipulation
open DY.Core.Trace.Arithmetic
open DY.Core.Trace.Arithmetic.Derived
open DY.Core.Bytes.Type
open DY.Core.Label.Type

open FStar.Set

#set-options "--fuel 0 --ifuel 1"

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

#push-options "--fuel 1"
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
#pop-options

#push-options "--fuel 1"
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
#pop-options

val traceful_modifies :
  #a:Type -> traceful a -> trace ->
  modifies_set
let traceful_modifies f tr_in =
  let (_, tr_out) = f tr_in in
  trace_modifies (tr_out <--> tr_in)


/// These predicates are shorthand for the commonly useful
/// statement that a given address is not modified by a given
/// trace or traceful function.

unfold
val trace_does_not_modify_addr :
  #label_t:Type -> principal -> state_id ->
  tr:trace_ label_t -> prop
let trace_does_not_modify_addr prin sid tr =
  ~((prin, sid) `mem` (trace_modifies tr))

unfold
val traceful_does_not_modify_addr :
  #a:Type -> principal -> state_id ->
  f:traceful a -> tr:trace -> prop
let traceful_does_not_modify_addr prin sid f tr =
  ~((prin, sid) `mem` (traceful_modifies f tr))

// TODO: Which of this and the previous definition is more useful?
// Simple cases can usually guarantee the stronger forall traces
// property, but that may be more difficult to work with in general.
val traceful_never_modifies_addr:
  #a:Type -> principal -> state_id ->
  f:traceful a -> prop
let traceful_never_modifies_addr prin sid f =
  forall tr. ~((prin, sid) `mem` (traceful_modifies f tr))


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

val traceful_modifies_option_bind :
  #a:Type -> #b:Type ->
  x:traceful (option a) -> f:(a -> traceful (option b)) ->
  tr_in:trace ->
  Lemma
  (ensures (
    let (y, tr_mid) = x tr_in in
    traceful_modifies ((let*?) x f) tr_in ==
    (match y with
    | None -> traceful_modifies x tr_in
    | Some y -> (union (traceful_modifies x tr_in) (traceful_modifies (f y) tr_mid))
    )
  ))
  [SMTPat (traceful_modifies ((let*?) x f) tr_in)]
let traceful_modifies_option_bind x f tr_in =
  let (y, tr_mid) = x tr_in in
  match y with
  | None -> ()
  | Some y -> (
    let (_, tr_out) = f y tr_mid in
    // Triggers trace_subtract_concat_slices
    assert(((tr_mid <--> tr_in) <++> (tr_out <--> tr_mid)) == (tr_out <--> tr_in))
  )

#push-options "--fuel 1"
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
#pop-options

val traceful_modifies_guard_tr :
  b:bool -> tr:trace ->
  Lemma (traceful_modifies (guard_tr b) tr == empty)
  [SMTPat (traceful_modifies (guard_tr b) tr)]
let traceful_modifies_guard_tr b tr = ()

#push-options "--fuel 2"
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
#pop-options

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

#push-options "--fuel 1"
val traceful_modifies_recv_msg :
  ts:timestamp -> tr:trace ->
  Lemma (traceful_modifies (recv_msg ts) tr == empty)
  [SMTPat (traceful_modifies (recv_msg ts) tr)]
let traceful_modifies_recv_msg ts tr = ()
#pop-options

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

#push-options "--fuel 1"
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
#pop-options

val traceful_modifies_trigger_event :
  prin:principal -> tag:string -> b:bytes -> tr:trace ->
  Lemma (traceful_modifies (trigger_event prin tag b) tr == empty)
  [SMTPat (traceful_modifies (trigger_event prin tag b) tr)]
let traceful_modifies_trigger_event prin tag b tr =
  reveal_opaque (`%trigger_event) (trigger_event)

/// The following two lemmas allow us to propagate the is_most_recent_state_for predicate
/// when a given address is unmodified.

val is_most_recent_state_for_later :
  prin:principal -> sid:state_id ->
  content_opt:option bytes ->
  tr1:trace -> tr2:trace ->
  Lemma
  (requires tr1 <$ tr2 /\
    is_most_recent_state_for prin sid content_opt tr1 /\
    trace_does_not_modify_addr prin sid (tr2 <--> tr1)
  )
  (ensures is_most_recent_state_for prin sid content_opt tr2)
  [SMTPat (tr1 <$ tr2);
   SMTPat (is_most_recent_state_for prin sid content_opt tr2);
   SMTPat (trace_does_not_modify_addr prin sid (tr2 <--> tr1));
  ]
let is_most_recent_state_for_later prin sid content_opt tr1 tr2 =
  reveal_opaque (`%is_most_recent_state_for) is_most_recent_state_for;
  let ts_opt = trace_search_last (tr2 <--> tr1) (is_state_for prin sid) in
  introduce Some? ts_opt ==> False
  with _. begin
    let SetState _ _ _ = get_entry_at (tr2 <--> tr1) (Some?.v ts_opt) in
    trace_modifies_spec (tr2 <--> tr1) prin sid
  end;
  trace_search_last_subtract tr1 tr2 (is_state_for prin sid);
  ()

val traceful_is_most_recent_state_for_later :
  (#a:Type) -> prin:principal -> sid:state_id ->
  content_opt:option bytes ->
  f:traceful a -> tr:trace ->
  Lemma
  (requires is_most_recent_state_for prin sid content_opt tr /\
    traceful_does_not_modify_addr prin sid f tr
  )
  (ensures (
    let (_, tr_out) = f tr in
    is_most_recent_state_for prin sid content_opt tr_out
  ))
  [SMTPat (f tr);
   SMTPat (is_most_recent_state_for prin sid content_opt tr);
   SMTPat (traceful_does_not_modify_addr prin sid f tr);
  ]
let traceful_is_most_recent_state_for_later prin sid content_opt f tr =
  let (_, tr_out) = f tr in
  // Triggers is_most_recent_state_for_later
  assert(trace_does_not_modify_addr prin sid (tr_out <--> tr));
  ()
