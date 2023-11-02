module DY.Core.Trace.Manipulation

open DY.Core.Trace.Type
open DY.Core.Trace.Invariant
open DY.Core.Bytes.Type
open DY.Core.Bytes
open DY.Core.Label.Type

#set-options "--fuel 1 --ifuel 1"

(*** Trace monad ***)

type crypto a = tr_in:trace -> out:(a & trace){tr_in <$ snd out}

val (let*): #a:Type -> #b:Type -> x:crypto a -> f:(a -> crypto b) -> crypto b
let (let*) #a #b x f tr =
  let (x', tr) = x tr in
  let (y, tr) = f x' tr in
  (y, tr)

val (let?): #a:Type -> #b:Type -> x:option a -> (y:a -> Pure (option b) (requires x == Some y) (ensures fun _ -> True)) -> option b
let (let?) #a #b x f =
  match x with
  | None -> None
  | Some x -> f x

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
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  (x, tr)

val get_trace: crypto trace
let get_trace tr =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  (tr, tr)

val guard: b:bool -> option unit
let guard b =
  if b then Some ()
  else None

// Some inversion lemmas to keep ifuel low
val invert_crypto:
  a:Type ->
  Lemma
  (inversion (a & trace))
  [SMTPat (crypto a)]
let invert_crypto a =
  allow_inversion (a & trace)

val invert_crypto_option:
  a:Type ->
  Lemma
  (inversion (option a))
  [SMTPat (crypto (option a))]
let invert_crypto_option a =
  allow_inversion (option a)

(*** Generic trace manipulation ***)

val add_event: trace_event -> crypto unit
let add_event e tr =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  ((), Snoc tr e)

val get_time: crypto nat
let get_time =
  let* tr = get_trace in
  return (DY.Core.Trace.Type.length tr)

(*** Sending messages ***)

[@@ "opaque_to_smt"]
val send_msg: bytes -> crypto nat
let send_msg msg =
  let* time = get_time in
  add_event (MsgSent msg);*
  return time

val send_msg_invariant:
  invs:protocol_invariants ->
  msg:bytes -> tr:trace ->
  Lemma
  (requires
    is_publishable invs.crypto_invs tr msg /\
    trace_invariant invs tr
  )
  (ensures (
    let (i, tr_out) = send_msg msg tr in
    trace_invariant invs tr_out /\
    event_at tr_out i (MsgSent msg)
  ))
  [SMTPat (send_msg msg tr); SMTPat (trace_invariant invs tr)]
let send_msg_invariant invs msg tr =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  reveal_opaque (`%send_msg) (send_msg)

[@@ "opaque_to_smt"]
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
  invs:protocol_invariants ->
  i:nat -> tr:trace ->
  Lemma
  (requires trace_invariant invs tr)
  (ensures (
    let (opt_msg, tr_out) = recv_msg i tr in
    tr_out == tr /\ (
      match opt_msg with
      | None -> True
      | Some msg -> is_publishable invs.crypto_invs tr msg
    )
  ))
  [SMTPat (recv_msg i tr);
   SMTPat (trace_invariant invs tr)
  ]
let recv_msg_invariant invs i tr =
  normalize_term_spec recv_msg;
  let (opt_msg, _) = recv_msg i tr in
  match opt_msg with
  | None -> ()
  | Some msg -> (
    msg_sent_on_network_are_publishable invs tr msg
  )

(*** Corruption ***)

[@@ "opaque_to_smt"]
val corrupt: principal -> nat -> crypto unit
let corrupt prin sess_id =
  add_event (Corrupt prin sess_id)

val corrupt_invariant:
  invs:protocol_invariants ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant invs tr
  )
  (ensures (
    let ((), tr_out) = corrupt prin sess_id tr in
    trace_invariant invs tr_out
  ))
  [SMTPat (corrupt prin sess_id tr); SMTPat (trace_invariant invs tr)]
let corrupt_invariant invs prin sess_id tr =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  normalize_term_spec corrupt

(*** Random number generation ***)

[@@ "opaque_to_smt"]
val mk_rand: usg:usage -> lab:label -> len:nat{len <> 0} -> crypto bytes
let mk_rand usg lab len =
  let* time = get_time in
  add_event (RandGen usg lab len);*
  return (Rand usg lab len time)

#push-options "--z3rlimit 25"
val mk_rand_trace_invariant:
  invs:protocol_invariants ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (requires trace_invariant invs tr)
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    trace_invariant invs tr_out /\
    1 <= DY.Core.Trace.Type.length tr_out /\
    rand_generated_at tr_out (DY.Core.Trace.Type.length tr_out - 1) b
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant invs tr)]
let mk_rand_trace_invariant invs usg lab len tr =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  reveal_opaque (`%mk_rand) (mk_rand)
#pop-options

val mk_rand_bytes_invariant:
  invs:protocol_invariants ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    bytes_invariant invs.crypto_invs tr_out b
  ))
  // We need a way for the SMT pattern to know the value of `invs`
  // This is done using `trace_invariant`, although it is not necessary for the theorem to hold,
  // It is certainly around in the context
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant invs tr)]
let mk_rand_bytes_invariant invs usg lab len tr =
  reveal_opaque (`%mk_rand) (mk_rand);
  normalize_term_spec bytes_invariant

val mk_rand_get_label:
  invs:protocol_invariants ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    get_label invs.crypto_invs.usages b == lab
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant invs tr)]
let mk_rand_get_label invs usg lab len tr =
  reveal_opaque (`%mk_rand) (mk_rand);
  normalize_term_spec get_label

val mk_rand_get_usage:
  invs:protocol_invariants ->
  usg:usage -> lab:label -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = mk_rand usg lab len tr in
    get_usage invs.crypto_invs.usages b == usg
  ))
  [SMTPat (mk_rand usg lab len tr); SMTPat (trace_invariant invs tr)]
let mk_rand_get_usage invs usg lab len tr =
  normalize_term_spec mk_rand;
  normalize_term_spec get_usage

(*** State ***)

[@@ "opaque_to_smt"]
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

[@@ "opaque_to_smt"]
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

[@@ "opaque_to_smt"]
val get_state: principal -> nat -> crypto (option bytes)
let get_state prin sess_id =
  let* tr = get_trace in
  return (get_state_aux prin sess_id tr)

val new_session_id_invariant:
  invs:protocol_invariants ->
  prin:principal -> tr:trace ->
  Lemma
  (requires trace_invariant invs tr)
  (ensures (
    let (_, tr_out) = new_session_id prin tr in
    tr == tr_out
  ))
  [SMTPat (new_session_id prin tr); SMTPat (trace_invariant invs tr)]
let new_session_id_invariant invs prin tr =
  normalize_term_spec new_session_id

#push-options "--z3rlimit 15"
val set_state_invariant:
  invs:protocol_invariants ->
  prin:principal -> sess_id:nat -> content:bytes -> tr:trace ->
  Lemma
  (requires
    invs.trace_invs.state_pred.pred tr prin sess_id content /\
    trace_invariant invs tr
  )
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    trace_invariant invs tr_out /\
    state_was_set tr_out prin sess_id content
  ))
  [SMTPat (set_state prin sess_id content tr); SMTPat (trace_invariant invs tr)]
let set_state_invariant invs prin sess_id content tr =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  normalize_term_spec set_state
#pop-options

val get_state_aux_state_invariant:
  invs:protocol_invariants ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant invs tr
  )
  (ensures (
    match get_state_aux prin sess_id tr with
    | None -> True
    | Some content -> invs.trace_invs.state_pred.pred tr prin sess_id content
  ))
let rec get_state_aux_state_invariant invs prin sess_id tr =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr with
  | Nil -> ()
  | Snoc tr_init (SetState prin' sess_id' content) -> (
    if prin = prin' && sess_id = sess_id' then (
      invs.trace_invs.state_pred.pred_later tr_init tr prin sess_id content
    ) else (
      get_state_aux_state_invariant invs prin sess_id tr_init;
      match get_state_aux prin sess_id tr_init with
      | None -> ()
      | Some content -> invs.trace_invs.state_pred.pred_later tr_init tr prin sess_id content
    )
  )
  | Snoc tr_init _ ->
    get_state_aux_state_invariant invs prin sess_id tr_init;
    match get_state_aux prin sess_id tr_init with
    | None -> ()
    | Some content -> invs.trace_invs.state_pred.pred_later tr_init tr prin sess_id content

val get_state_state_invariant:
  invs:protocol_invariants ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant invs tr
  )
  (ensures (
    let (opt_content, tr_out) = get_state prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> invs.trace_invs.state_pred.pred tr prin sess_id content
    )
  ))
  [SMTPat (get_state prin sess_id tr); SMTPat (trace_invariant invs tr)]
let get_state_state_invariant invs prin sess_id tr =
  normalize_term_spec get_state;
  get_state_aux_state_invariant invs prin sess_id tr

(*** Event triggering ***)

[@@ "opaque_to_smt"]
val trigger_event: principal -> string -> bytes -> crypto unit
let trigger_event prin tag content =
  add_event (Event prin tag content)

val trigger_event_trace_invariant:
  invs:protocol_invariants ->
  prin:principal -> tag:string -> content:bytes -> tr:trace ->
  Lemma
  (requires
    invs.trace_invs.event_pred tr prin tag content /\
    trace_invariant invs tr
  )
  (ensures (
    let ((), tr_out) = trigger_event prin tag content tr in
    trace_invariant invs tr_out /\
    event_triggered tr_out prin tag content
  ))
  [SMTPat (trigger_event prin tag content tr); SMTPat (trace_invariant invs tr)]
let trigger_event_trace_invariant invs prin tag content tr =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  normalize_term_spec trigger_event
