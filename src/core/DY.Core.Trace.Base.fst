module DY.Core.Trace.Base

open DY.Core.Trace.Type
open DY.Core.Bytes.Type
open DY.Core.Label.Type

/// Shorthands for trace and trace events.

type trace_event = trace_event_ label
type trace = trace_ label

/// The length of a trace.

val length: #label_t:Type -> trace_ label_t -> nat
let rec length tr =
  match tr with
  | Nil -> 0
  | Snoc init last -> length init + 1

/// a type macro for timestamps (indices on the trace)

type timestamp = nat

(*** Prefix and trace_ extension ***)

/// Compute the prefix of a trace.

[@@ "opaque_to_smt"]
val prefix: #label_t:Type -> tr:trace_ label_t -> i:timestamp{i <= length tr} -> trace_ label_t
let rec prefix tr i =
  if length tr = i then
    tr
  else
    let Snoc tr_init _ = tr in
    prefix tr_init i

/// Express whether a trace is the extension of another.
/// This is a crucial relation between traces,
/// because the trace only grows during a protocol execution.

[@@ "opaque_to_smt"]
val grows: #label_t:Type -> trace_ label_t -> trace_ label_t -> prop
let grows tr1 tr2 =
  length tr1 <= length tr2 /\
  tr1 == prefix tr2 (length tr1)

/// It is used a lot in DY*, therefore we define an operator shorthand.

let (<$) = grows

val grows_induction_principle:
  #label_t:Type ->
  p:(trace_ label_t -> prop) ->
  (tr:trace_ label_t -> ev:trace_event_ label_t -> Lemma (requires p tr) (ensures p (Snoc tr ev))) ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma
  (requires
    p tr1 /\
    tr1 <$ tr2
  )
  (ensures p tr2)
let rec grows_induction_principle #label_t p pf tr1 tr2 =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
  if length tr1 = length tr2 then ()
  else (
    let Snoc init2 last2 = tr2 in
    grows_induction_principle p pf tr1 init2;
    pf init2 last2
  )

/// The relation <$ is reflexive.

val grows_reflexive:
  tr:trace ->
  Lemma (tr <$ tr)
  [SMTPat (tr <$ tr)]
let grows_reflexive tr =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label)

/// The relation <$ is transitive.

val grows_transitive:
  tr1:trace -> tr2:trace -> tr3:trace ->
  Lemma
  (requires tr1 <$ tr2 /\ tr2 <$ tr3)
  (ensures tr1 <$ tr3)
  [SMTPat (tr1 <$ tr2); SMTPat (tr1 <$ tr3)]
let rec grows_transitive tr1 tr2 tr3 =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  if length tr2 >= length tr3 then
    ()
  else (
    let Snoc tr3_init _ = tr3 in
    grows_transitive tr1 tr2 tr3_init
  )

/// The prefix function outputs traces of the correct length.

val length_prefix:
  tr:trace -> i:timestamp{i <= length tr} ->
  Lemma
  (ensures length (prefix tr i) == i)
  [SMTPat (length (prefix tr i))]
let rec length_prefix tr i =
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  if length tr = i then ()
  else
    let Snoc tr_init _ = tr in
    length_prefix tr_init i

/// A trace which is the prefix of another is shorter.

val length_grows:
  tr1:trace -> tr2:trace ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures length tr1 <= length tr2)
  [SMTPat (tr1 <$ tr2)]
let length_grows tr1 tr2 =
  reveal_opaque (`%grows) (grows #label)

/// The prefix function outputs traces that are prefixes of the input.

val prefix_grows:
  tr:trace -> i:timestamp{i <= length tr} ->
  Lemma
  (ensures (prefix tr i) <$ tr)
  //TODO: is this SMTPat dangerous? Should we restrict it to the "safe" on below?
  [SMTPat (prefix tr i)]
  //[SMTPat ((prefix tr i) <$ tr)]
let prefix_grows tr i =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label)

val prefix_prefix_grows:
  tr1:trace -> tr2:trace -> i1:timestamp -> i2:timestamp ->
  Lemma
  (requires
    tr1 <$ tr2 /\
    i1 <= length tr1 /\
    i2 <= length tr2 /\
    i1 <= i2
  )
  (ensures prefix tr1 i1 <$ prefix tr2 i2)
  [SMTPat (prefix tr1 i1 <$ prefix tr2 i2)]
  // Alternative SMT pattern if the above one doesn't trigger enough
  // [SMTPat (prefix tr1 i1);
  //  SMTPat (prefix tr2 i2);
  //  SMTPat (tr1 <$ tr2)]
let rec prefix_prefix_grows tr1 tr2 i1 i2 =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  if i2 = length tr2 then ()
  else if length tr1 = length tr2 then (
    let Snoc tr1_init _ = tr1 in
    let Snoc tr2_init _ = tr2 in
    prefix_prefix_grows tr1_init tr2_init i1 i2
  ) else (
    let Snoc tr2_init _ = tr2 in
    prefix_prefix_grows tr1 tr2_init i1 i2
  )

val prefix_prefix_eq:
  tr1:trace -> tr2:trace -> i:timestamp ->
  Lemma
  (requires
    tr1 <$ tr2 /\
    i <= length tr1
  )
  (ensures prefix tr1 i == prefix tr2 i)
  [SMTPat (prefix tr1 i);
   SMTPat (prefix tr2 i);
   SMTPat (tr1 <$ tr2)]
let rec prefix_prefix_eq tr1 tr2 i =
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  if length tr1 = length tr2 then ()
  else (
    let Snoc tr2_init _ = tr2 in
    prefix_prefix_eq tr1 tr2_init i
  )

(*** Event in the trace predicates ***)

/// Retrieve the event at some timestamp in the trace.

val get_event_at:
  #label_t:Type ->
  tr:trace_ label_t -> i:timestamp{i < length tr} ->
  trace_event_ label_t
let rec get_event_at tr i =
  if i+1 = length tr then
    let Snoc _ last = tr in
    last
  else (
    let Snoc tr_init _ = tr in
    get_event_at tr_init i
  )

/// Has some particular event been triggered at a some particular timestamp in the trace?

val event_at:
  #label_t:Type ->
  trace_ label_t -> timestamp -> trace_event_ label_t ->
  prop
let event_at tr i e =
  if i >= length tr then
    False
  else
    e == get_event_at tr i

/// Has some particular event been triggered in the trace (at any timestamp)?

val event_exists:
  #label_t:Type ->
  trace_ label_t -> trace_event_ label_t ->
  prop
let event_exists tr e =
  exists i. event_at tr i e

/// An event in the trace stays here when the trace grows.

val event_at_grows:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  i:timestamp -> e:trace_event_ label_t ->
  Lemma
  (requires event_at tr1 i e /\ tr1 <$ tr2)
  (ensures event_at tr2 i e)
  [SMTPat (event_at tr1 i e); SMTPat (tr1 <$ tr2)]
let rec event_at_grows #label_t tr1 tr2 i e =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
  if i >= length tr1 then ()
  else if length tr1 >= length tr2 then ()
  else (
    let Snoc tr2_init _ = tr2 in
    event_at_grows tr1 tr2_init i e
  )

val event_exists_grows:
  #label_t:Type -> 
  tr1:trace_ label_t -> tr2:trace_ label_t -> 
  e:trace_event_ label_t ->
  Lemma
  (requires
    tr1 <$ tr2 /\ event_exists tr1 e
  )
  (ensures
    event_exists tr2 e
  )
let event_exists_grows tr1 tr2 e =  ()

val last_entry_exists:
  #label_t:Type ->
  tr:trace_ label_t ->
  Lemma
    (requires Snoc? tr )
    (ensures (
       let Snoc _ last = tr in
       event_exists tr last
    ))
    [SMTPat (Snoc? tr)]
let last_entry_exists tr = 
  let Snoc _ last = tr in
  assert(event_at tr (length tr - 1) last)

/// Shorthand predicates.

/// Has a message been sent on the network?

val msg_sent_on_network: trace -> bytes -> prop
let msg_sent_on_network tr msg =
  event_exists tr (MsgSent msg)

/// Has some state been stored by a principal?

val state_was_set: trace -> principal -> state_id -> bytes -> prop
let state_was_set tr prin sess_id content =
  event_exists tr (SetState prin sess_id content)

/// Has a principal been corrupt?

val was_corrupt: #label_t:Type -> trace_ label_t -> principal -> state_id -> prop
let was_corrupt tr prin sess_id =
  event_exists tr (Corrupt prin sess_id)

/// Has a (custom, protocol-specific) event been triggered at some timestamp?

val event_triggered_at: trace -> timestamp -> principal -> string -> bytes -> prop
let event_triggered_at tr i prin tag content =
  event_at tr i (Event prin tag content)

/// Has a (custom, protocol-specific) event been triggered (at any timestamp)?

val event_triggered: trace -> principal -> string -> bytes -> prop
let event_triggered tr prin tag content =
  exists i. event_triggered_at tr i prin tag content

/// An event being triggered at some time stays triggered as the trace grows.

val event_triggered_grows:
  tr1:trace -> tr2:trace ->
  prin:principal -> tag:string -> content:bytes  ->
  Lemma
  (requires event_triggered tr1 prin tag content /\ tr1 <$ tr2)
  (ensures event_triggered tr2 prin tag content)
  [SMTPat (event_triggered tr1 prin tag content); SMTPat (tr1 <$ tr2)]
let event_triggered_grows tr1 tr2 prin tag content = ()

/// Has a random bytestring been generated at some timestamp?

val rand_generated_at: trace -> timestamp -> bytes -> prop
let rand_generated_at tr i b =
  match b with
  | Rand usg len time ->
    time == i /\ (exists lab. event_at tr i (RandGen usg lab len))
  | _ -> False

(*** Forgetting labels ***)

/// Functions to replace labels in a trace by `()`.
/// This is useful to use labels that are predicates on `trace_ unit`
/// with actual traces that are `trace_ label`.
/// See `DY.Core.Label.Type` for more information.
/// This is defined using a `fmap` function on traces,
/// which can help proving properties on `trace_forget_labels`.
/// It is named after Haskell's fmap `(a -> b) -> f a -> f b`,
/// where here `f` is either `trace_event_` or `trace_`.
/// Furthermore, `a` and `b` are types for labels
/// (in practice either `label` or `unit`),
/// and the `a -> b` function is applied on labels in the trace.

val fmap_trace_event:
  #a:Type -> #b:Type ->
  (a -> b) -> trace_event_ a ->
  trace_event_ b
let fmap_trace_event #a #b f ev =
  match ev with
  | MsgSent msg -> MsgSent msg
  | RandGen usg lab len -> RandGen usg (f lab) len
  | Corrupt prin sess_id -> Corrupt prin sess_id
  | SetState prin sess_id content -> SetState prin sess_id content
  | Event prin tag content -> Event prin tag content

val fmap_trace:
  #a:Type -> #b:Type ->
  (a -> b) -> trace_ a ->
  trace_ b
let rec fmap_trace f tr =
  match tr with
  | Nil -> Nil
  | Snoc init last ->
    Snoc (fmap_trace f init) (fmap_trace_event f last)

val forget_label:
  #a:Type -> #b:Type ->
  b ->
  a -> b
let forget_label #a #b x _ = x

val trace_forget_labels:
  trace ->
  trace_ unit
let trace_forget_labels tr =
  fmap_trace (forget_label ()) tr

val fmap_trace_identity:
  #a:Type ->
  f:(a -> a) ->
  tr:trace_ a ->
  Lemma
  (requires forall x. f x == x)
  (ensures fmap_trace f tr == tr)
let rec fmap_trace_identity #a f tr =
  match tr with
  | Nil -> ()
  | Snoc init last ->
    fmap_trace_identity f init

val fmap_trace_compose:
  #a:Type -> #b:Type -> #c:Type ->
  f:(a -> b) -> g:(b -> c) -> h:(a -> c) ->
  tr:trace_ a ->
  Lemma
  (requires forall x. g (f x) == h x)
  (ensures fmap_trace g (fmap_trace f tr) == fmap_trace h tr)
let rec fmap_trace_compose #a #b #c f g h tr =
  match tr with
  | Nil -> ()
  | Snoc init last ->
    fmap_trace_compose f g h init

val length_trace_forget_labels:
  tr:trace ->
  Lemma (length (trace_forget_labels tr) == length tr)
let rec length_trace_forget_labels tr =
  match tr with
  | Nil -> ()
  | Snoc init last -> length_trace_forget_labels init

val trace_forget_labels_later:
  tr1:trace -> tr2:trace ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures (trace_forget_labels tr1) <$ (trace_forget_labels tr2))
let rec trace_forget_labels_later tr1 tr2 =
  reveal_opaque (`%grows) (grows #unit);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #unit);
  reveal_opaque (`%grows) (grows #label);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  if length tr1 = length tr2 then (
    match tr1, tr2 with
    | Nil, Nil -> ()
    | Snoc tr1_init _, Snoc tr2_init _ -> ()
  ) else (
    let Snoc tr2_init tr2_last = tr2 in
    trace_forget_labels_later tr1 tr2_init
  )
