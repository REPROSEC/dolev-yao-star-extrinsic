module DY.Core.Trace.Manipulation

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.Invariant
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type

#set-options "--fuel 1 --ifuel 1"

/// This module defines the lightweight trace monad `traceful`,
/// various trace-manipulation functions and
/// corresponding invariant preservation theorems.

(*** Trace monad ***)

/// The lightweight trace monad is a state monad on the trace.
/// Furthermore, the trace is required to grow:
/// a traceful function can only append entries to the trace.

type traceful a = tr_in:trace -> out:(a & trace){tr_in <$ snd out}

/// Bind operator for the trace monad

val (let*): #a:Type -> #b:Type -> x:traceful a -> f:(a -> traceful b) -> traceful b
let (let*) #a #b x f tr =
  let (x', tr) = x tr in
  let (y, tr) = f x' tr in
  (y, tr)

/// Bind operator for the option monad.
/// The `Pure` effect is a trick found by Son Ho to allow some kind of intrinsic proofs,
/// for example to be able to do:
///   let? x = Some y in
///   let Some y' = x in
/// In the second line of code, without the Pure annotation,
/// F* wouldn't be able to tell that `x` is a `Some`.

val (let?): #a:Type -> #b:Type -> x:option a -> (y:a -> Pure (option b) (requires x == Some y) (ensures fun _ -> True)) -> option b
let (let?) #a #b x f =
  match x with
  | None -> None
  | Some x -> f x

/// Bind operator for the trace + option monad.

val (let*?): #a:Type -> #b:Type -> x:traceful (option a) -> f:(a -> traceful (option b)) -> traceful (option b)
let (let*?) #a #b x f tr0 =
  let (opt_x', tr) = x tr0 in
  match opt_x' with
  | None -> (None, tr)
  | Some x' -> (
    let (y, tr) = f x' tr in
    (y, tr)
  )

/// return function for the trace monad.

val return: #a:Type -> a -> traceful a
let return #a x tr =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  (x, tr)

/// getter for the trace monad.

val get_trace: traceful trace
let get_trace tr =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  (tr, tr)

/// guard function for the option monad.

val guard: b:bool -> option (squash b)
let guard b =
  if b
  then Some ()
  else None

/// guard function for the traceful + option monad

val guard_tr : (b:bool) -> traceful (option (squash b))
let guard_tr b =
  return (guard b)


// Some inversion lemmas to keep ifuel low.
// See FStarLang/FStar#3076 for more information.

val invert_traceful:
  a:Type ->
  Lemma
  (inversion (a & trace))
  [SMTPat (traceful a)]
let invert_traceful a =
  allow_inversion (a & trace)

val invert_traceful_option:
  a:Type ->
  Lemma
  (inversion (option a))
  [SMTPat (traceful (option a))]
let invert_traceful_option a =
  allow_inversion (option a)

(*** Generic trace manipulation ***)

/// Internal function: add a trace entry to the trace.

val add_entry: trace_entry -> traceful unit
let add_entry e tr =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  ((), Snoc tr e)

val add_entry_entry_exists:
  e:trace_entry -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = add_entry e tr in
    entry_exists tr_out e
  ))
let add_entry_entry_exists e tr = ()

/// Adding a trace entry preserves the trace invariant
/// when the trace entry satisfy the invariant.

val add_entry_invariant:
  {|protocol_invariants|} ->
  e:trace_entry -> tr:trace ->
  Lemma
  (requires
    trace_entry_invariant tr e /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = add_entry e tr in
    trace_invariant tr_out
  ))
let add_entry_invariant #invs e tr =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant)

/// Get the current time (i.e. trace length).

val get_time: traceful timestamp
let get_time =
  let* tr = get_trace in
  return (trace_length tr)

(*** Sending messages ***)

/// Send a message on the network.

[@@ "opaque_to_smt"]
val send_msg: bytes -> traceful timestamp
let send_msg msg =
  let* time = get_time in
  add_entry (MsgSent msg);*
  return time

val send_msg_msg_entry:
  msg:bytes -> tr:trace ->
  Lemma
  (ensures (
    let (i, tr_out) = send_msg msg tr in
    entry_at tr_out i (MsgSent msg)
  ))
 [SMTPat (send_msg msg tr);]
let send_msg_msg_entry msg tr =
 reveal_opaque (`%send_msg) (send_msg)


/// Sending a message on the network preserves the trace invariant
/// when the message is publishable.

val send_msg_invariant:
  {|protocol_invariants|} ->
  msg:bytes -> tr:trace ->
  Lemma
  (requires
    is_publishable tr msg /\
    trace_invariant tr
  )
  (ensures (
    let (i, tr_out) = send_msg msg tr in
    trace_invariant tr_out
  ))
  [SMTPat (send_msg msg tr); SMTPat (trace_invariant tr)]
let send_msg_invariant #invs msg tr =
  add_entry_invariant (MsgSent msg) tr;
  reveal_opaque (`%send_msg) (send_msg)

/// Receive a message from the network.

[@@ "opaque_to_smt"]
val recv_msg: timestamp -> traceful (option bytes)
let recv_msg i =
  let* tr = get_trace in
  if i < trace_length tr then
    match get_entry_at tr i with
    | MsgSent msg -> return (Some msg)
    | _ -> return None
  else
    return None


val recv_msg_same_trace:
  i:timestamp -> tr:trace ->
  Lemma
  (ensures (
    let (opt_msg, tr_out) = recv_msg i tr in
    tr_out == tr
  ))
  [SMTPat (recv_msg i tr);]
let recv_msg_same_trace i tr =
  reveal_opaque (`%recv_msg) recv_msg

/// When the trace invariant holds,
/// received messages are publishable.

val recv_msg_invariant:
  {|protocol_invariants|} ->
  i:timestamp -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_msg, tr_out) = recv_msg i tr in
      match opt_msg with
      | None -> True
      | Some msg -> is_publishable tr msg
  ))
  [SMTPat (recv_msg i tr);
   SMTPat (trace_invariant tr)
  ]
let recv_msg_invariant #invs i tr =
  normalize_term_spec recv_msg;
  let (opt_msg, _) = recv_msg i tr in
  match opt_msg with
  | None -> ()
  | Some msg -> (
    msg_sent_on_network_are_publishable tr msg
  )

(*** Corruption ***)

/// Corrupt a state set at a given timestamp

[@@ "opaque_to_smt"]
val corrupt: timestamp -> traceful unit
let corrupt time =
  add_entry (Corrupt time)

/// Corrupting a state always preserve the trace invariant.

val corrupt_invariant:
  {|protocol_invariants|} ->
  time:timestamp -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = corrupt time tr in
    trace_invariant tr_out
  ))
  [SMTPat (corrupt time tr); SMTPat (trace_invariant tr)]
let corrupt_invariant #invs time tr =
  add_entry_invariant (Corrupt time) tr;
  normalize_term_spec corrupt

(*** Random number generation ***)

/// Generate a random bytestring.

[@@ "opaque_to_smt"]
val mk_rand: usg:usage -> lab:label -> len:nat{len <> 0} -> traceful bytes
let mk_rand usg lab len =
  let* time = get_time in
  add_entry (RandGen usg lab len);*
  return (Rand len time)


val mk_rand_rand_gen_at_end:
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    rand_just_generated tr_out b
  ))
  [SMTPat (mk_rand usg lab len tr);]
let mk_rand_rand_gen_at_end usg lab len tr =
  reveal_opaque (`%mk_rand) (mk_rand)


/// Generating a random bytestrings always preserve the trace invariant.

val mk_rand_trace_invariant:
  {|protocol_invariants|} ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    trace_invariant tr_out
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let mk_rand_trace_invariant #invs usg lab len tr =
  add_entry_invariant (RandGen usg lab len) tr;
  reveal_opaque (`%mk_rand) (mk_rand)

/// Random bytestrings satisfy the bytes invariant.

val mk_rand_bytes_invariant:
  {|protocol_invariants|} ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    bytes_invariant tr_out b
  ))
  // We need a way for the SMT pattern to know the value of `invs`
  // This is done using `trace_invariant`, although it is not necessary for the theorem to hold,
  // it is certainly around in the context
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let mk_rand_bytes_invariant #invs usg lab len tr =
  reveal_opaque (`%mk_rand) (mk_rand);
  normalize_term_spec bytes_invariant

/// Label of random bytestrings.

val mk_rand_get_label:
  {|protocol_invariants|} ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    get_label tr_out b == lab
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let mk_rand_get_label #invs usg lab len tr =
  reveal_opaque (`%mk_rand) (mk_rand);
  normalize_term_spec get_label

/// Usage of random bytestrings.

val mk_rand_has_usage:
  {|protocol_invariants|} ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    b `has_usage tr_out` usg
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let mk_rand_has_usage #invs usg lab len tr =
  normalize_term_spec mk_rand;
  normalize_term_spec has_usage

// Stronger version of the lemma above, if needed
val mk_rand_get_usage:
  {|protocol_invariants|} ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    get_usage tr_out b == usg
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let mk_rand_get_usage #invs usg lab len tr =
  reveal_opaque (`%mk_rand) (mk_rand);
  normalize_term_spec get_usage


(*** State ***)

/// Set the state of a principal at a given state identifier.

[@@ "opaque_to_smt"]
val set_state: principal -> state_id -> bytes -> traceful unit
let set_state prin session_id content =
  add_entry (SetState prin session_id content)

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
  | Snoc tr_init entry -> (
    match entry with
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
  (requires entry_exists tr (SetState prin sess_id state_content))
  (ensures sess_id.the_id < (compute_new_session_id prin tr).the_id)
let rec compute_new_session_id_correct prin tr sess_id state_content =
  match tr with
  | Nil -> ()
  | Snoc tr_init entry -> (
    match entry with
    | SetState prin' sess_id' state_content' ->
      if prin = prin' && sess_id = sess_id' && state_content = state_content' then ()
      else (
        compute_new_session_id_correct prin tr_init sess_id state_content
      )
    | _ -> compute_new_session_id_correct prin tr_init sess_id state_content
  )

/// Compute a fresh state identifier for a principal.

[@@ "opaque_to_smt"]
val new_session_id: principal -> traceful state_id
let new_session_id prin =
  let* tr = get_trace in
  return (compute_new_session_id prin tr)

val get_state_aux: principal -> state_id -> tr:trace -> option bytes
let get_state_aux prin sess_id tr =
  let? state_ts = trace_search_last tr (is_state_for prin sess_id) in
  let SetState _ _ content = get_entry_at tr state_ts in
  Some content

/// Retrieve the state stored by a principal at some state identifier.

[@@ "opaque_to_smt"]
val get_state: principal -> state_id -> traceful (option bytes)
let get_state prin sess_id =
  let* tr = get_trace in
  return (get_state_aux prin sess_id tr)

/// Obtaining a new state identifier do not change the trace.

val new_session_id_same_trace:
  prin:principal -> tr:trace ->
  Lemma
  (ensures (
    let (_, tr_out) = new_session_id prin tr in
    tr == tr_out
  ))
  [SMTPat (new_session_id prin tr)]
let new_session_id_same_trace prin tr =
  normalize_term_spec new_session_id

val set_state_is_most_recent_state_for:
  prin:principal -> sess_id:state_id ->
  content:bytes -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    is_most_recent_state_for prin sess_id (Some content) tr_out
  ))
  [SMTPat (set_state prin sess_id content tr);]
let set_state_is_most_recent_state_for prin sess_id content tr =
  reveal_opaque (`%set_state) (set_state);
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for);
  ()

val set_state_state_was_set:
  prin:principal -> sess_id:state_id -> content:bytes -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    state_was_set tr_out prin sess_id content
  ))
  [SMTPat (set_state prin sess_id content tr);]
let set_state_state_was_set prin sess_id content tr =
  normalize_term_spec set_state


/// Storing a state preserves the trace invariant
/// when the state satisfy the state predicate.

val set_state_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> content:bytes -> tr:trace ->
  Lemma
  (requires
    state_pred.pred tr prin sess_id content /\
    (
      let content_old_opt = get_state_aux prin sess_id tr in
      Some? content_old_opt ==>
      state_update_pred.update_pred tr prin sess_id (Some?.v content_old_opt) content
    ) /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    trace_invariant tr_out
  ))
  [SMTPat (set_state prin sess_id content tr); SMTPat (trace_invariant tr)]
let set_state_invariant #invs prin sess_id content tr =
  add_entry_invariant (SetState prin sess_id content) tr;
  normalize_term_spec set_state

val get_state_same_trace:
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = get_state prin sess_id tr in
    tr == tr_out
  ))
  [SMTPat (get_state prin sess_id tr);]
let get_state_same_trace prin sess_id tr =
  reveal_opaque (`%get_state) get_state

val is_most_recent_state_for_get_state:
  prin:principal -> sess_id:state_id ->
  content_opt:option bytes -> tr:trace ->
  Lemma
  (requires is_most_recent_state_for prin sess_id content_opt tr)
  (ensures (
    let (content_opt', _) = get_state prin sess_id tr in
    content_opt == content_opt'
  ))
  [SMTPat (is_most_recent_state_for prin sess_id content_opt tr);
   SMTPat (get_state prin sess_id tr);
  ]
let is_most_recent_state_for_get_state prin sess_id content_opt tr =
  reveal_opaque (`%get_state) (get_state);
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for);
  ()

val get_state_is_most_recent_state_for:
  prin:principal -> sess_id:state_id ->
  tr:trace ->
  Lemma
  (ensures (
    let (content_opt, tr_out) = get_state prin sess_id tr in
    is_most_recent_state_for prin sess_id content_opt tr
  ))
  [SMTPat (get_state prin sess_id tr);]
let get_state_is_most_recent_state_for prin sess_id tr =
  reveal_opaque (`%get_state) (get_state);
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for);
  ()

#push-options "--ifuel 1"
val get_state_aux_state_was_set:
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (ensures (
    match get_state_aux prin sess_id tr with
    | None -> True
    | Some content ->
        state_was_set tr prin sess_id content
  ))
let get_state_aux_state_was_set prin sess_id tr = ()
#pop-options

val get_state_state_was_set:
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = get_state prin sess_id tr in
    match opt_content with
    | None -> True
    | Some content ->
        state_was_set tr prin sess_id content
  ))
  [SMTPat (get_state prin sess_id tr)]
let get_state_state_was_set prin sess_id tr =
  reveal_opaque (`%get_state) get_state;
  get_state_aux_state_was_set prin sess_id tr

(*** Event triggering ***)

/// Trigger a protocol event.

[@@ "opaque_to_smt"]
val trigger_event: principal -> string -> bytes -> traceful unit
let trigger_event prin tag content =
  add_entry (Event prin tag content)

val trigger_event_event_triggered:
  prin:principal -> tag:string -> content:bytes -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = trigger_event prin tag content tr in
    event_triggered tr_out prin tag content
  ))
  [SMTPat (trigger_event prin tag content tr);]
let trigger_event_event_triggered prin tag content tr =
  reveal_opaque (`%trigger_event) trigger_event;
  let ((), tr_out) = trigger_event prin tag content tr in
  assert(event_triggered_at tr_out (trace_length tr) prin tag content)

/// Triggering a protocol event preserves the trace invariant
/// when the protocol event satisfy the event predicate.

val trigger_event_trace_invariant:
  {|protocol_invariants|} ->
  prin:principal -> tag:string -> content:bytes -> tr:trace ->
  Lemma
  (requires
    event_pred tr prin tag content /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = trigger_event prin tag content tr in
    trace_invariant tr_out
  ))
  [SMTPat (trigger_event prin tag content tr); SMTPat (trace_invariant tr)]
let trigger_event_trace_invariant #invs prin tag content tr =
  add_entry_invariant (Event prin tag content) tr;
  normalize_term_spec trigger_event
