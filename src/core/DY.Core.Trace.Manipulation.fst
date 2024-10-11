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
/// a traceful function can only append events to the trace.

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

/// Internal function: add a trace event to the trace.

val add_event: trace_event -> traceful unit
let add_event e tr =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  ((), Snoc tr e)

/// Adding a trace event preserves the trace invariant
/// when the trace event satisfy the invariant.

val add_event_invariant:
  {|protocol_invariants|} ->
  e:trace_event -> tr:trace ->
  Lemma
  (requires
    trace_event_invariant tr e /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = add_event e tr in
    trace_invariant tr_out /\
    event_exists tr_out e
  ))
let add_event_invariant #invs e tr =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant)

/// Get the current time (i.e. trace length).

val get_time: traceful timestamp
let get_time =
  let* tr = get_trace in
  return (DY.Core.Trace.Base.length tr)

(*** Sending messages ***)

/// Send a message on the network.

[@@ "opaque_to_smt"]
val send_msg: bytes -> traceful timestamp
let send_msg msg =
  let* time = get_time in
  add_event (MsgSent msg);*
  return time

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
    trace_invariant tr_out /\
    event_at tr_out i (MsgSent msg)
  ))
  [SMTPat (send_msg msg tr); SMTPat (trace_invariant tr)]
let send_msg_invariant #invs msg tr =
  add_event_invariant (MsgSent msg) tr;
  reveal_opaque (`%send_msg) (send_msg)

/// Receive a message from the network.

[@@ "opaque_to_smt"]
val recv_msg: timestamp -> traceful (option bytes)
let recv_msg i =
  let* tr = get_trace in
  if i < DY.Core.Trace.Base.length tr then
    match get_event_at tr i with
    | MsgSent msg -> return (Some msg)
    | _ -> return None
  else
    return None

/// When the trace invariant holds,
/// received messages are publishable.

val recv_msg_invariant:
  {|protocol_invariants|} ->
  i:timestamp -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_msg, tr_out) = recv_msg i tr in
    tr_out == tr /\ (
      match opt_msg with
      | None -> True
      | Some msg -> is_publishable tr msg
    )
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

/// Corrupt a session of a principal.

[@@ "opaque_to_smt"]
val corrupt: principal -> state_id -> traceful unit
let corrupt prin sess_id =
  add_event (Corrupt prin sess_id)

/// Corrupting a principal always preserve the trace invariant.

val corrupt_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = corrupt prin sess_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (corrupt prin sess_id tr); SMTPat (trace_invariant tr)]
let corrupt_invariant #invs prin sess_id tr =
  add_event_invariant (Corrupt prin sess_id) tr;
  normalize_term_spec corrupt

(*** Random number generation ***)

/// Generate a random bytestring.

[@@ "opaque_to_smt"]
val mk_rand: usg:usage -> lab:label -> len:nat{len <> 0} -> traceful bytes
let mk_rand usg lab len =
  let* time = get_time in
  add_event (RandGen usg lab len);*
  return (Rand usg len time)

/// Generating a random bytestrings always preserve the trace invariant.

#push-options "--z3rlimit 25"
val mk_rand_trace_invariant:
  {|protocol_invariants|} ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    trace_invariant tr_out /\
    1 <= DY.Core.Trace.Base.length tr_out /\
    rand_generated_at tr_out (DY.Core.Trace.Base.length tr_out - 1) b
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let mk_rand_trace_invariant #invs usg lab len tr =
  add_event_invariant (RandGen usg lab len) tr;
  reveal_opaque (`%mk_rand) (mk_rand)
#pop-options

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

val mk_rand_get_usage:
  {|protocol_invariants|} ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    get_usage b == usg
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let mk_rand_get_usage #invs usg lab len tr =
  normalize_term_spec mk_rand;
  normalize_term_spec get_usage

(*** State ***)


val state_was_set_grows:
  tr1:trace -> tr2:trace ->
  p:principal -> sid:state_id -> content:bytes ->
  Lemma
  (requires
    tr1 <$ tr2
    /\ state_was_set tr1 p sid content
  )
  (ensures
    state_was_set tr2 p sid content
  )
let state_was_set_grows tr1 tr2 p sid content = ()

/// Set the state of a principal at a given state identifier.

[@@ "opaque_to_smt"]
val set_state: principal -> state_id -> bytes -> traceful unit
let set_state prin session_id content =
  add_event (SetState prin session_id content)

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
    match evt with
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

val get_state_aux: principal -> state_id -> trace -> option bytes
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

/// Retrieve the state stored by a principal at some state identifier.

[@@ "opaque_to_smt"]
val get_state: principal -> state_id -> traceful (option bytes)
let get_state prin sess_id =
  let* tr = get_trace in
  return (get_state_aux prin sess_id tr)

/// Obtaining a new state identifier do not change the trace.

val new_session_id_invariant:
  prin:principal -> tr:trace ->
  Lemma
  (ensures (
    let (_, tr_out) = new_session_id prin tr in
    tr == tr_out
  ))
  [SMTPat (new_session_id prin tr)]
let new_session_id_invariant prin tr =
  normalize_term_spec new_session_id

/// Storing a state preserves the trace invariant
/// when the state satisfy the state predicate.

#push-options "--z3rlimit 15"
val set_state_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> content:bytes -> tr:trace ->
  Lemma
  (requires
    state_pred.pred tr prin sess_id content /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    trace_invariant tr_out /\
    state_was_set tr_out prin sess_id content
  ))
  [SMTPat (set_state prin sess_id content tr); SMTPat (trace_invariant tr)]
let set_state_invariant #invs prin sess_id content tr =
  add_event_invariant (SetState prin sess_id content) tr;
  normalize_term_spec set_state
#pop-options

val get_state_aux_state_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    match get_state_aux prin sess_id tr with
    | None -> True
    | Some content -> 
           state_pred.pred tr prin sess_id content
           /\ state_was_set tr prin sess_id content
  ))
let rec get_state_aux_state_invariant #invs prin sess_id tr =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  match tr with
  | Nil -> ()
  | Snoc tr_init (SetState prin' sess_id' content) -> (
    if prin = prin' && sess_id = sess_id' then (
      state_pred.pred_later tr_init tr prin sess_id content
    ) else (
      get_state_aux_state_invariant prin sess_id tr_init;
      match get_state_aux prin sess_id tr_init with
      | None -> ()
      | Some content -> state_pred.pred_later tr_init tr prin sess_id content
    )
  )
  | Snoc tr_init _ ->
    get_state_aux_state_invariant prin sess_id tr_init;
    match get_state_aux prin sess_id tr_init with
    | None -> ()
    | Some content -> state_pred.pred_later tr_init tr prin sess_id content

/// When the trace invariant holds,
/// retrieved states satisfy the state predicate.

val get_state_state_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (opt_content, tr_out) = get_state prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> 
             state_pred.pred tr prin sess_id content
             /\ state_was_set tr prin sess_id content
    )
  ))
  [SMTPat (get_state prin sess_id tr); SMTPat (trace_invariant tr)]
let get_state_state_invariant #invs prin sess_id tr =
  normalize_term_spec get_state;
  get_state_aux_state_invariant prin sess_id tr


/// Lookup the most recent state of a principal satisfying some property.
/// Returns the state and corresponding state id,
/// or `None` if no such state exists.

val lookup_state_aux: principal -> (bytes -> bool) -> trace -> option (bytes & state_id)
let rec lookup_state_aux prin p tr =
  match tr with
  | Nil -> None
  | Snoc rest (SetState prin' sid' cont') ->
      if prin' = prin && p cont'
      then Some (cont', sid')
      else lookup_state_aux prin p rest
  | Snoc rest _ -> lookup_state_aux prin p rest

val lookup_state: principal -> (bytes -> bool) -> traceful (option (bytes & state_id))
let lookup_state prin p =
  let* tr = get_trace in
  return (lookup_state_aux prin p tr)

/// If `lookup` returns some state,
/// this state satisfies the property used in the lookup.

val lookup_state_aux_state_was_set_and_prop:
  prin:principal -> p:(bytes -> bool) -> tr:trace ->
  Lemma
  (ensures (
    let opt_content = lookup_state_aux prin p tr in
      match opt_content with
      | None -> True
      | Some (content, sid) ->
               p content
             /\ state_was_set tr prin sid content
  ))
let rec lookup_state_aux_state_was_set_and_prop prin p tr =
  match tr with
  | Nil -> ()
  | Snoc tr_init _ ->
         lookup_state_aux_state_was_set_and_prop prin p tr_init

/// If `lookup` returns a state on a trace with `trace_invariant`,
/// the returned state additionally satisfies the state predicate.

val lookup_state_aux_state_invariant:
  {|protocol_invariants|} ->
  prin:principal -> p:(bytes -> bool) -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let opt_content = lookup_state_aux prin p tr in
      match opt_content with
      | None -> True
      | Some (content, sid) ->
               state_pred.pred tr prin sid content
             /\ p content
             /\ state_was_set tr prin sid content
  ))
let lookup_state_aux_state_invariant #invs prin p tr =
  lookup_state_aux_state_was_set_and_prop prin p tr;
  match lookup_state_aux prin p tr with
  | None -> ()
  | Some (content, sid) ->
    state_was_set_implies_pred tr prin sid content

/// lifting both properties from `_aux` to the `traceful` versions.

val lookup_state_state_was_set_and_prop:
  prin:principal -> p:(bytes -> bool) -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = lookup_state prin p tr in
    tr == tr_out /\
    (match opt_content with
     | None -> True
     | Some (content, sid) ->
              p content
            /\ state_was_set tr prin sid content
    )
  ))
  [SMTPat (lookup_state prin p tr)]
let lookup_state_state_was_set_and_prop prin p tr =
  lookup_state_aux_state_was_set_and_prop prin p tr


val lookup_state_state_invariant:
  {|invs:protocol_invariants|} ->
  prin:principal -> p:(bytes -> bool) -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (opt_content, tr_out) = lookup_state prin p tr in
    tr == tr_out /\
    (match opt_content with
     | None -> True
     | Some (content, sid) ->
              state_pred.pred tr prin sid content
            /\ p content
            /\ state_was_set tr prin sid content
    )
  ))
  [SMTPat (lookup_state prin p tr); SMTPat (trace_invariant #invs tr)]
let lookup_state_state_invariant #invs prin p tr =
  lookup_state_aux_state_invariant prin p tr

(*** Event triggering ***)

/// Trigger a protocol event.

[@@ "opaque_to_smt"]
val trigger_event: principal -> string -> bytes -> traceful unit
let trigger_event prin tag content =
  add_event (Event prin tag content)

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
    trace_invariant tr_out /\
    event_triggered tr_out prin tag content
  ))
  [SMTPat (trigger_event prin tag content tr); SMTPat (trace_invariant tr)]
let trigger_event_trace_invariant #invs prin tag content tr =
  add_event_invariant (Event prin tag content) tr;
  normalize_term_spec trigger_event
