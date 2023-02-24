module DY.Core.Trace.Manipulation

open DY.Core.Trace.Type
open DY.Core.Trace.Invariant
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type

(*** Trace monad ***)

type crypto a = tr_in:trace -> (a & tr_out:trace{tr_in <$ tr_out})

val (let*): #a:Type -> #b:Type -> x:crypto a -> f:(a -> crypto b) -> crypto b
let (let*) #a #b x f tr =
  let (x', tr) = x tr in
  let (y, tr) = f x' tr in
  (y, tr)

val (let*?): #a:Type -> #b:Type -> x:crypto (option a) -> f:(a -> crypto (option b)) -> crypto (option b)
let (let*?) #a #b x f tr0 =
  let (opt_x', tr) = x tr0 in
  match opt_x' with
  | None -> (None, tr)
  | Some x' -> (
    let (y, tr) = f x' tr in
    (y, tr)
  )

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

val send_msg: bytes -> crypto nat
let send_msg msg =
  let* time = get_time in
  add_event (MsgSent msg);*
  return time

val send_msg_invariant:
  preds:protocol_predicates ->
  msg:bytes -> tr:trace ->
  Lemma
  (requires
    is_publishable preds.crypto_preds tr msg /\
    trace_invariant preds tr
  )
  (ensures (
    let (i, tr_out) = send_msg msg tr in
    trace_invariant preds tr_out /\
    event_at tr_out i (MsgSent msg)
  ))
  [SMTPat (send_msg msg tr); SMTPat (trace_invariant preds tr)]
let send_msg_invariant preds msg tr = ()

val recv_msg: nat -> crypto (option bytes)
let recv_msg i =
  let* tr = get_trace in
  if i < DY.Core.Trace.Type.length tr then
    match get_event_at tr i with
    | MsgSent msg -> return (Some msg)
    | _ -> return None
  else
    return None

val recv_msg_invariant:
  preds:protocol_predicates ->
  i:nat -> tr:trace ->
  Lemma
  (requires trace_invariant preds tr)
  (ensures (
    let (opt_msg, tr_out) = recv_msg i tr in
    tr_out == tr /\ (
      match opt_msg with
      | None -> True
      | Some msg -> is_publishable preds.crypto_preds tr msg
    )
  ))
  [SMTPat (recv_msg i tr);
   SMTPat (trace_invariant preds tr)
  ]
let recv_msg_invariant preds i tr =
  let (opt_msg, _) = recv_msg i tr in
  match opt_msg with
  | None -> ()
  | Some msg -> (
    msg_sent_on_network_are_publishable preds tr msg
  )

(*** Corruption ***)

val corrupt: principal -> nat -> crypto unit
let corrupt prin sess_id =
  add_event (Corrupt prin sess_id)

val corrupt_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr
  )
  (ensures (
    let ((), tr_out) = corrupt prin sess_id tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (corrupt prin sess_id tr); SMTPat (trace_invariant preds tr)]
let corrupt_invariant preds prin sess_id tr = ()

(*** Random number generation ***)

val mk_rand: lab:label -> len:nat{len <> 0} -> crypto bytes
let mk_rand lab len =
  let* time = get_time in
  add_event (RandGen lab len);*
  return (Rand lab len time)

val mk_rand_trace_invariant:
  preds:protocol_predicates ->
  lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (requires trace_invariant preds tr)
  (ensures (
    let (b, tr_out) = mk_rand lab len tr in
    trace_invariant preds tr_out /\
    rand_generated_at tr_out (DY.Core.Trace.Type.length tr_out - 1) b
  ))
  [SMTPat (mk_rand lab len tr); SMTPat (trace_invariant preds tr)]
let mk_rand_trace_invariant preds lab len tr = ()

val mk_rand_bytes_invariant:
  preds:protocol_predicates ->
  lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand lab len tr in
    bytes_invariant preds.crypto_preds tr_out b
  ))
  // We need a way for the SMT pattern to know the value of `preds`
  // This is done using `trace_invariant`, although it is not necessary for the theorem to hold,
  // It is certainly around in the context
  [SMTPat (mk_rand lab len tr); SMTPat (trace_invariant preds tr)]
let mk_rand_bytes_invariant preds lab len tr = ()

val mk_rand_get_label:
  lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand lab len tr in
    get_label b == lab
  ))
  [SMTPat (mk_rand lab len tr)]
let mk_rand_get_label lab len tr = ()

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

val get_state_aux: principal -> nat -> trace -> option bytes
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

val get_state: principal -> nat -> crypto (option bytes)
let get_state prin sess_id =
  let* tr = get_trace in
  return (get_state_aux prin sess_id tr)

val set_state_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> content:bytes -> tr:trace ->
  Lemma
  (requires
    preds.trace_preds.state_pred.pred tr prin sess_id content /\
    trace_invariant preds tr
  )
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    trace_invariant preds tr_out /\
    state_was_set tr_out prin sess_id content
  ))
  [SMTPat (set_state prin sess_id content tr); SMTPat (trace_invariant preds tr)]
let set_state_invariant preds prin sess_id content tr = ()

val get_state_aux_state_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr
  )
  (ensures (
    match get_state_aux prin sess_id tr with
    | None -> True
    | Some content -> preds.trace_preds.state_pred.pred tr prin sess_id content
  ))
let rec get_state_aux_state_invariant preds prin sess_id tr =
  match tr with
  | Nil -> ()
  | Snoc tr_init (SetState prin' sess_id' content) -> (
    if prin = prin' && sess_id = sess_id' then (
      preds.trace_preds.state_pred.pred_later tr_init tr prin sess_id content
    ) else (
      get_state_aux_state_invariant preds prin sess_id tr_init;
      match get_state_aux prin sess_id tr_init with
      | None -> ()
      | Some content -> preds.trace_preds.state_pred.pred_later tr_init tr prin sess_id content
    )
  )
  | Snoc tr_init _ ->
    get_state_aux_state_invariant preds prin sess_id tr_init;
    match get_state_aux prin sess_id tr_init with
    | None -> ()
    | Some content -> preds.trace_preds.state_pred.pred_later tr_init tr prin sess_id content

val get_state_state_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr
  )
  (ensures (
    let (opt_content, tr_out) = get_state prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> preds.trace_preds.state_pred.pred tr prin sess_id content
    )
  ))
  [SMTPat (get_state prin sess_id tr); SMTPat (trace_invariant preds tr)]
let get_state_state_invariant preds prin sess_id tr =
  get_state_aux_state_invariant preds prin sess_id tr

(*** Event triggering ***)

val trigger_event: principal -> string -> bytes -> crypto unit
let trigger_event prin tag content =
  add_event (Event prin tag content)

val trigger_event_trace_invariant:
  preds:protocol_predicates ->
  prin:principal -> tag:string -> content:bytes -> tr:trace ->
  Lemma
  (requires
    preds.trace_preds.event_pred tr prin tag content /\
    trace_invariant preds tr
  )
  (ensures (
    let ((), tr_out) = trigger_event prin tag content tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (trigger_event prin tag content tr); SMTPat (trace_invariant preds tr)]
let trigger_event_trace_invariant preds prin tag content tr = ()
