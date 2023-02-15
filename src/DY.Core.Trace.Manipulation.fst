module DY.Core.Trace.Manipulation

open DY.Core.Trace.Type
open DY.Core.Trace.Invariant
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type

(*** Trace monad ***)

type crypto a = tr_in:trace -> (a & tr_out:trace{tr_in <$ tr_out})

val (let*): #a:Type -> #b:Type -> x:crypto a -> f:(a -> crypto b) -> crypto b
let (let*) #a #b x f tr0 =
  let (x', tr1) = x tr0 in
  let (y, tr2) = f x' tr1 in
  (y, tr2)

val return: #a:Type -> a -> crypto a
let return #a x tr =
  (x, tr)

val get_trace: crypto trace
let get_trace tr =
  (tr, tr)

(*** Generic trace manipulation ***)

val add_event: trace_event -> crypto unit
let add_event e tr =
  ((), Snoc tr e)

val event_exists_add_event:
  e:trace_event -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = add_event e tr in
    event_exists tr_out e
  ))
  [SMTPat (add_event e tr)]
let event_exists_add_event e tr = ()

val get_time: crypto nat
let get_time =
  let* tr = get_trace in
  return (DY.Core.Trace.Type.length tr)

(*** Sending messages ***)

val send_msg: bytes -> crypto unit
let send_msg msg =
  add_event (MsgSent msg)

val send_msg_invariant:
  pr:protocol_preds ->
  msg:bytes -> tr:trace ->
  Lemma
  (requires
    is_publishable pr tr msg /\
    trace_invariant pr tr
  )
  (ensures (
    let ((), tr_out) = send_msg msg tr in
    trace_invariant pr tr_out
  ))
  [SMTPat (send_msg msg tr); SMTPat (trace_invariant pr tr)]
let send_msg_invariant pr msg tr = ()

(*** Corruption ***)

val corrupt: pre_pre_label -> crypto unit
let corrupt who =
  add_event (Corrupt who)

val corrupt_invariant:
  pr:protocol_preds ->
  who:pre_pre_label -> tr:trace ->
  Lemma
  (requires
    trace_invariant pr tr
  )
  (ensures (
    let ((), tr_out) = corrupt who tr in
    trace_invariant pr tr_out
  ))
  [SMTPat (corrupt who tr); SMTPat (trace_invariant pr tr)]
let corrupt_invariant pr msg tr = ()

(*** Random number generation ***)

val mk_rand: lab:label -> len:nat{len <> 0} -> crypto bytes
let mk_rand lab len =
  let* time = get_time in
  add_event RandGen;*
  return (Rand lab len time)

val mk_rand_trace_invariant:
  pr:protocol_preds ->
  lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (requires trace_invariant pr tr)
  (ensures (
    let (b, tr_out) = mk_rand lab len tr in
    trace_invariant pr tr_out
  ))
  [SMTPat (mk_rand lab len tr); SMTPat (trace_invariant pr tr)]
let mk_rand_trace_invariant pr lab len tr = ()

val mk_rand_bytes_invariant:
  pr:protocol_preds ->
  lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand lab len tr in
    bytes_invariant pr tr_out b
  ))
  // We need a way for the SMT pattern to know the value of `pr`
  // This is done using `trace_invariant`, although it is not necessary for the theorem to hold,
  // It is certainly around in the context
  [SMTPat (mk_rand lab len tr); SMTPat (trace_invariant pr tr)]
let mk_rand_bytes_invariant pr lab len tr =
  ()

(*** State ***)

val set_state: principal -> nat -> bytes -> crypto unit
let set_state prin session_id content =
  add_event (SetState prin session_id content)

val max: int -> int -> int
let max x y =
  if x < y then y else x

val compute_new_session_id: principal -> trace -> nat
let rec compute_new_session_id prin tr =
  match tr with
  | Nil -> 0
  | Snoc tr_init evt -> (
    match evt with
    | SetState prin' sess_id _ ->
      if prin = prin' then
        max (sess_id+1) (compute_new_session_id prin tr_init)
      else
        compute_new_session_id prin tr_init
    | _ -> compute_new_session_id prin tr_init
  )

// Sanity check
val compute_new_session_id_correct:
  prin:principal -> tr:trace ->
  sess_id:nat -> state_content:bytes ->
  Lemma
  (requires event_exists tr (SetState prin sess_id state_content))
  (ensures sess_id < compute_new_session_id prin tr)
let rec compute_new_session_id_correct prin tr sess_id state_content =
  match tr with
  | Nil -> ()
  | Snoc tr_init evt -> (
    if evt = SetState prin sess_id state_content then ()
    else (
      compute_new_session_id_correct prin tr_init sess_id state_content
    )
  )

val new_session_id: principal -> crypto nat
let new_session_id prin =
  let* tr = get_trace in
  return (compute_new_session_id prin tr)

val new_state: principal -> bytes -> crypto nat
let new_state prin content =
  let* sess_id = new_session_id prin in
  set_state prin sess_id content;*
  return sess_id

//TODO: invariant preservation
