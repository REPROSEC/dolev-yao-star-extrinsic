module DY.Core.Trace.Base

open DY.Core.Trace.Type
open DY.Core.Bytes.Type
open DY.Core.Label.Type
module L = FStar.List.Tot.Base

#set-options "--fuel 1 --ifuel 1"

/// Shorthands for trace and trace entries.

type trace_entry = trace_entry_ label
type trace = trace_ label

/// The length of a trace.

val trace_length: #label_t:Type -> trace_ label_t -> nat
let rec trace_length tr =
  match tr with
  | Nil -> 0
  | Snoc init last -> trace_length init + 1

/// Is a given timestamp on a given trace?
val on_trace: #label_t:Type -> timestamp -> trace_ label_t -> bool
let on_trace ts tr = ts < trace_length tr

(*** Hiding constructors ***)

val empty_trace : #label_t:Type -> trace_ label_t 
let empty_trace = Nil

val is_empty: #label_t:Type -> trace_ label_t -> bool
let is_empty = Nil?

val is_not_empty: #label_t:Type -> trace_ label_t -> bool
let is_not_empty = Snoc?

val is_not_empty_trace_length:
  #label_t:Type ->
  tr:trace_ label_t ->
  Lemma
  (is_not_empty tr <==> 0 < trace_length tr)
  [SMTPat (is_not_empty tr)]
let is_not_empty_trace_length tr = ()

val init : #label_t:Type -> tr:trace_ label_t{is_not_empty tr} -> trace_ label_t
let init tr =
  let Snoc init _ = tr in
  init

val last: #label_t:Type -> tr:trace_ label_t{is_not_empty tr} -> trace_entry_ label_t
let last tr =
  let Snoc _ en = tr in
  en

// to be used infix: tr `append_entry` entry
val append_entry: #label_t:Type -> trace_ label_t -> trace_entry_ label_t -> trace_ label_t
let append_entry tr en = Snoc tr en


/// The last valid timestamp on a given trace. Used in recursive
/// functions that operate on timestamp to avoid the need for explicit
/// + 1 and - 1 when checking for the end of a trace.
val last_timestamp: #label_t:Type -> tr:trace_ label_t{is_not_empty tr} -> timestamp
let last_timestamp tr = trace_length tr - 1

(*** From/To List Conversion ***)

val trace_from_rev_list: #label_t:Type -> list (trace_entry_ label_t) -> trace_ label_t
let rec trace_from_rev_list entries =
  match entries with
  | [] -> Nil
  | hd::tl -> Snoc (trace_from_rev_list tl) hd

/// generate a trace from a list,
/// where the first element of the list,
/// is the first element of the trace
val trace_from_list: #label_t:Type -> list (trace_entry_ label_t) -> trace_ label_t
let trace_from_list ens = trace_from_rev_list (L.rev ens)


let rec trace_to_rev_list tr =
  match tr with
  | Nil -> []
  | Snoc init last -> last:: trace_to_rev_list init

/// generate a list from a trace,
/// where the last trace entry
/// is the last entry in the list
let trace_to_list tr =
  L.rev (trace_to_rev_list tr)


(*** Prefix and trace_ extension ***)

/// Compute the prefix of a trace.

[@@ "opaque_to_smt"]
val prefix: #label_t:Type -> tr:trace_ label_t -> i:timestamp{i <= trace_length tr} -> trace_ label_t
let rec prefix #label_t tr i =
  if trace_length tr = i then
    tr
  else
    prefix (init tr) i

/// Express whether a trace is the extension of another.
/// This is a crucial relation between traces,
/// because the trace only grows during a protocol execution.

[@@ "opaque_to_smt"]
val grows: #label_t:Type -> trace_ label_t -> trace_ label_t -> prop
let grows #label_t tr1 tr2 =
  trace_length tr1 <= trace_length tr2 /\
  tr1 == prefix tr2 (trace_length tr1)

/// It is used a lot in DY*, therefore we define an operator shorthand.

let (<$) = grows

val grows_induction_principle:
  #label_t:Type ->
  p:(trace_ label_t -> prop) ->
  (tr:trace_ label_t -> entry:trace_entry_ label_t -> Lemma (requires p tr) (ensures p (Snoc tr entry))) ->
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
  if trace_length tr1 = trace_length tr2 then ()
  else (
    let Snoc init2 last2 = tr2 in
    grows_induction_principle p pf tr1 init2;
    pf init2 last2
  )

/// The relation <$ is reflexive.

val grows_reflexive:
  #label_t:Type ->
  tr:trace_ label_t ->
  Lemma (tr <$ tr)
  [SMTPat (tr <$ tr)]
let grows_reflexive #label_t tr =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t)

/// The relation <$ is transitive.

val grows_transitive:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t -> tr3:trace_ label_t ->
  Lemma
  (requires tr1 <$ tr2 /\ tr2 <$ tr3)
  (ensures tr1 <$ tr3)
  [SMTPat (tr1 <$ tr2); SMTPat (tr1 <$ tr3)]
let rec grows_transitive #label_t tr1 tr2 tr3 =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
  if trace_length tr2 >= trace_length tr3 then
    ()
  else
    grows_transitive tr1 tr2 (init tr3)

/// The prefix function outputs traces of the correct trace_length.

val trace_length_prefix:
  #label_t:Type ->
  tr:trace_ label_t -> i:timestamp{i <= trace_length tr} ->
  Lemma
  (ensures trace_length (prefix tr i) == i)
  [SMTPat (trace_length (prefix tr i))]
let rec trace_length_prefix #label_t tr i =
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
  if trace_length tr = i then ()
  else
    trace_length_prefix (init tr) i

/// A trace which is the prefix of another is shorter.

val trace_length_grows:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures trace_length tr1 <= trace_length tr2)
  [SMTPat (tr1 <$ tr2)]
let trace_length_grows #label_t tr1 tr2 =
  reveal_opaque (`%grows) (grows #label_t)

/// The prefix function outputs traces that are prefixes of the input.

val prefix_grows:
  #label_t:Type ->
  tr:trace_ label_t -> i:timestamp{i <= trace_length tr} ->
  Lemma
  (ensures (prefix tr i) <$ tr)
  //TODO: is this SMTPat dangerous? Should we restrict it to the "safe" on below?
  [SMTPat (prefix tr i)]
  //[SMTPat ((prefix tr i) <$ tr)]
let prefix_grows #label_t tr i =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t)


/// The relation <$ has Nil (empty_trace) as a least element, and
/// is compatible with growing traces via Snoc (append_entry).
/// Note that these two lemmas use Nil and Snoc directly, rather than
/// empty_trace and append_entry, because this allows their SMTPats to
/// trigger more robustly.

let grows_nil (#label_t:Type) (tr:trace_ label_t)
  : Lemma (ensures Nil <$ tr)
    [SMTPat (Nil <$ tr)]
  = reveal_opaque (`%grows) (grows #label_t)

let grows_snoc (#label_t:Type) (tr:trace_ label_t) (e:trace_entry_ label_t)
  : Lemma (ensures tr <$ (Snoc tr e))
    [SMTPat (tr <$ (Snoc tr e))]
  = reveal_opaque (`%grows) (grows #label_t);
    norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t)


val prefix_prefix_grows:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t -> i1:timestamp -> i2:timestamp ->
  Lemma
  (requires
    tr1 <$ tr2 /\
    i1 <= trace_length tr1 /\
    i2 <= trace_length tr2 /\
    i1 <= i2
  )
  (ensures prefix tr1 i1 <$ prefix tr2 i2)
  [SMTPat (prefix tr1 i1 <$ prefix tr2 i2)]
  // Alternative SMT pattern if the above one doesn't trigger enough
  // [SMTPat (prefix tr1 i1);
  //  SMTPat (prefix tr2 i2);
  //  SMTPat (tr1 <$ tr2)]
let rec prefix_prefix_grows #label_t tr1 tr2 i1 i2 =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
  if i2 = trace_length tr2 then ()
  else if trace_length tr1 = trace_length tr2 then
    prefix_prefix_grows (init tr1) (init tr2) i1 i2
  else
    prefix_prefix_grows tr1 (init tr2) i1 i2

val prefix_prefix_eq:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t -> i:timestamp ->
  Lemma
  (requires
    tr1 <$ tr2 /\
    i <= trace_length tr1
  )
  (ensures prefix tr1 i == prefix tr2 i)
  [SMTPat (prefix tr1 i);
   SMTPat (prefix tr2 i);
   SMTPat (tr1 <$ tr2)]
let rec prefix_prefix_eq #label_t tr1 tr2 i =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
  if trace_length tr1 = trace_length tr2 then ()
  else
    prefix_prefix_eq tr1 (init tr2) i

/// Every trace is equal to its full-length prefix

let prefix_full_eq (#label_t:Type) (tr:trace_ label_t)
  : Lemma (ensures (prefix tr (trace_length tr) == tr))
    [SMTPat (prefix tr (trace_length tr))]
  = reveal_opaque (`%prefix) (prefix #label_t);
    norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t)

/// Two traces with the same length, where one is a prefix of the other, must be the same

let grows_full_eq (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2 /\ trace_length tr1 == trace_length tr2)
    (ensures tr1 == tr2)
  = prefix_prefix_eq tr1 tr2 (trace_length tr1)

/// The relation <$ is a non-strict partial order, and so if tr1 <$ tr2,
/// we can split into the case where tr1 and tr2 are equal, and that in which
/// tr1 is a strict prefix of tr2

let grows_cases (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2)
    (ensures tr1 == tr2 \/ (
      is_not_empty tr2 /\
      tr1 <$ (init tr2)
    ))
  = if trace_length tr1 = trace_length tr2
    then grows_full_eq tr1 tr2
    else begin
      let open FStar.Calc in
      calc (<$) {
        tr1;
        == {}
        prefix tr1 (trace_length tr1);
        <$ {}
        prefix tr2 (trace_length (init tr2));
        == { assert((init tr2) <$ tr2) } // Triggers prefix_prefix_eq (init tr2) tr2 (length (init tr2))
        prefix (init tr2) (trace_length (init tr2));
        == {}
        (init tr2);
      }
    end

(*** Entries in the trace predicates ***)

/// Retrieve the entry at some timestamp in the trace.

val get_entry_at:
  #label_t:Type ->
  tr:trace_ label_t -> i:timestamp{i `on_trace` tr} ->
  trace_entry_ label_t
let rec get_entry_at #label_t tr i =
  if i = last_timestamp tr then
    last tr
  else
    get_entry_at (init tr) i


val get_entry_at_last_timestamp_is_last:
  #label_t:Type ->
  tr:trace_ label_t{is_not_empty tr} ->
  Lemma
  (get_entry_at tr (last_timestamp tr) == last tr)
  [SMTPat (last tr)]
let get_entry_at_last_timestamp_is_last tr = ()

/// Has some particular entry been triggered at a some particular timestamp in the trace?

val entry_at:
  #label_t:Type ->
  trace_ label_t -> timestamp -> trace_entry_ label_t ->
  prop
let entry_at #label_t tr i e =
  i `on_trace` tr /\
  e == get_entry_at tr i

/// Has some particular entry been triggered in the trace (at any timestamp)?

val entry_exists:
  #label_t:Type ->
  trace_ label_t -> trace_entry_ label_t ->
  prop
let entry_exists #label_t tr e =
  exists i. entry_at tr i e

/// Is a given entry the last entry on the trace?

val trace_entry_just_occurred: #label_t:Type -> trace_ label_t -> trace_entry_ label_t -> prop
let trace_entry_just_occurred tr en =
  is_not_empty tr /\
  last tr == en



/// An entry in the trace stays here when the trace grows.

val get_entry_at_grows:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  i:timestamp{i `on_trace` tr1} ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures get_entry_at tr1 i == get_entry_at tr2 i)
  [SMTPat (get_entry_at tr1 i); SMTPat (tr1 <$ tr2)]
let rec get_entry_at_grows #label_t tr1 tr2 i =
  reveal_opaque (`%grows) (grows #label_t);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
  if  i `on_trace` tr1 && trace_length tr1 < trace_length tr2
  then get_entry_at_grows tr1 (init tr2) i
  else ()

val entry_at_grows:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  i:timestamp -> e:trace_entry_ label_t ->
  Lemma
  (requires entry_at tr1 i e /\ tr1 <$ tr2)
  (ensures entry_at tr2 i e)
  [SMTPat (entry_at tr1 i e); SMTPat (tr1 <$ tr2)]
let entry_at_grows #label_t tr1 tr2 i e = ()

/// The Snoc in the SMT pattern here is needed to make the lemma
/// trigger more robustly.
val last_entry_exists:
  #label_t:Type ->
  tr:trace_ label_t ->
  Lemma
    (requires is_not_empty tr)
    (ensures entry_exists tr (last tr))
    [SMTPat (Snoc? tr)]
let last_entry_exists tr =
  assert(entry_at tr (last_timestamp tr) (last tr))

/// Shorthand predicates.

/// Has a message been sent on the network?

val msg_sent_on_network:
  #label_t:Type ->
  trace_ label_t -> bytes ->
  prop
let msg_sent_on_network #label_t tr msg =
  entry_exists tr (MsgSent msg)

/// Has some state been stored by a principal?

val state_was_set:
  #label_t:Type ->
  trace_ label_t -> principal -> state_id -> bytes ->
  prop
let state_was_set #label_t tr prin sess_id content =
  entry_exists tr (SetState prin sess_id content)

/// Has a principal been corrupt?

val state_was_corrupt:
  #label_t:Type ->
  trace_ label_t -> principal -> state_id -> bytes ->
  prop
let state_was_corrupt tr prin sess_id content =
  exists time.
    entry_exists tr (Corrupt time) /\
    entry_at tr time (SetState prin sess_id content)

/// Has a (custom, protocol-specific) event been triggered at some timestamp?

val event_triggered_at:
  #label_t:Type ->
  trace_ label_t -> timestamp -> principal -> string -> bytes ->
  prop
let event_triggered_at #label_t tr i prin tag content =
  entry_at tr i (Event prin tag content)

/// Has a (custom, protocol-specific) event been triggered (at any timestamp)?

val event_triggered:
  #label_t:Type ->
  trace_ label_t -> principal -> string -> bytes ->
  prop
let event_triggered #label_t tr prin tag content =
  exists i. event_triggered_at tr i prin tag content

/// Find the timestamp at which an event has been triggered.
/// (Can be useful when debugging a proof.)

#push-options "--ifuel 1 --fuel 2 --z3rlimit 25"
val find_event_triggered_at_timestamp_opt:
  #label_t:Type ->
  tr:trace_ label_t -> prin:principal -> tag:string -> content:bytes ->
  Pure (option timestamp)
  (requires True)
  (ensures fun opt_i ->
    match opt_i with
    | Some i ->
      event_triggered_at tr i prin tag content /\
      ~(event_triggered (prefix tr i) prin tag content)
    | None -> ~(event_triggered tr prin tag content)
  )
let rec find_event_triggered_at_timestamp_opt #label_t tr prin tag content =
  match tr with
  | Nil -> None
  | Snoc init last ->
    match find_event_triggered_at_timestamp_opt init prin tag content with
    | Some i -> Some i
    | None -> (
      match last with
      | Event prin' tag' content' ->
        if prin = prin' && tag = tag' && content = content' then
          Some (trace_length init)
        else None
      | _ -> None
    )
#pop-options

[@@ "opaque_to_smt"]
val find_event_triggered_at_timestamp:
  #label_t:Type ->
  tr:trace_ label_t -> prin:principal -> tag:string -> content:bytes ->
  Pure timestamp
  (requires event_triggered tr prin tag content)
  (ensures fun i ->
    event_triggered_at tr i prin tag content /\
    ~(event_triggered (prefix tr i) prin tag content)
  )
let find_event_triggered_at_timestamp #label_t tr prin tag content =
  Some?.v (find_event_triggered_at_timestamp_opt tr prin tag content)

val find_event_triggered_at_timestamp_later:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  prin:principal -> tag:string -> content:bytes ->
  Lemma
  (requires
    event_triggered tr1 prin tag content /\
    tr1 <$ tr2
  )
  (ensures find_event_triggered_at_timestamp tr1 prin tag content == find_event_triggered_at_timestamp tr2 prin tag content)
  [SMTPat (find_event_triggered_at_timestamp tr1 prin tag content);
   SMTPat (find_event_triggered_at_timestamp tr2 prin tag content);
   SMTPat (tr1 <$ tr2)
  ]
let rec find_event_triggered_at_timestamp_later #label_t tr1 tr2 prin tag content =
  if trace_length tr1 = trace_length tr2 then ()
  else (
    reveal_opaque (`%grows) (grows #label_t);
    norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
    let Snoc init2 last2 = tr2 in
    find_event_triggered_at_timestamp_later tr1 init2 prin tag content
  )

/// An event being triggered at some time stays triggered as the trace grows.

val event_triggered_grows:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  prin:principal -> tag:string -> content:bytes  ->
  Lemma
  (requires event_triggered tr1 prin tag content /\ tr1 <$ tr2)
  (ensures event_triggered tr2 prin tag content)
  [SMTPat (event_triggered tr1 prin tag content); SMTPat (tr1 <$ tr2)]
let event_triggered_grows #label_t tr1 tr2 prin tag content = ()

/// Has a random bytestring been generated at some timestamp?

val rand_generated_at:
  #label_t:Type ->
  trace_ label_t -> timestamp -> bytes ->
  prop
let rand_generated_at #label_t tr i b =
  match b with
  | Rand len time ->
    time == i /\ (exists usg lab. entry_at tr i (RandGen usg lab len))
  | _ -> False


/// Was a random bytestring generated just now,
/// i.e., at the end of the trace?

val rand_just_generated: #label_t:Type -> trace_ label_t -> bytes -> prop
let rand_just_generated tr rand =
  is_not_empty tr /\
  rand_generated_at tr (last_timestamp tr) rand


(*** Forgetting labels ***)

/// Functions to replace labels in a trace by `()`.
/// This is useful to use labels that are predicates on `trace_ unit`
/// with actual traces that are `trace_ label`.
/// See `DY.Core.Label.Type` for more information.
/// This is defined using a `fmap` function on traces,
/// which can help proving properties on `trace_forget_labels`.
/// It is named after Haskell's fmap `(a -> b) -> f a -> f b`,
/// where here `f` is either `trace_entry_` or `trace_`.
/// Furthermore, `a` and `b` are types for labels
/// (in practice either `label` or `unit`),
/// and the `a -> b` function is applied on labels in the trace.

val fmap_trace_entry:
  #a:Type -> #b:Type ->
  (a -> b) -> trace_entry_ a ->
  trace_entry_ b
let fmap_trace_entry #a #b f entry =
  match entry with
  | MsgSent msg -> MsgSent msg
  | RandGen usg lab len -> RandGen usg (f lab) len
  | Corrupt time -> Corrupt time
  | SetState prin sess_id content -> SetState prin sess_id content
  | Event prin tag content -> Event prin tag content

val fmap_trace:
  #a:Type -> #b:Type ->
  (a -> b) -> trace_ a ->
  trace_ b
let rec fmap_trace #a #b f tr =
  match tr with
  | Nil -> Nil
  | Snoc init last ->
    Snoc (fmap_trace f init) (fmap_trace_entry f last)

val trace_length_fmap_trace:
  #a:Type -> #b:Type ->
  f:(a -> b) -> tr:trace_ a ->
  Lemma (trace_length (fmap_trace f tr) == trace_length tr)
  [SMTPat (trace_length (fmap_trace f tr))]
let rec trace_length_fmap_trace #a #b f tr =
  match tr with
  | Nil -> ()
  | Snoc init last -> trace_length_fmap_trace f init

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

val fmap_trace_prefix:
  #a:Type -> #b:Type ->
  f:(a -> b) ->
  tr:trace_ a -> i:timestamp{i <= trace_length tr} ->
  Lemma (
    prefix (fmap_trace f tr) i == fmap_trace f (prefix tr i)
  )
let rec fmap_trace_prefix #a #b f tr i =
  norm_spec [zeta; delta_only [`%prefix]] (prefix #a);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #b);
  if trace_length tr = i then ()
  else
    fmap_trace_prefix f (init tr) i

val fmap_trace_later:
  #a:Type -> #b:Type ->
  f:(a -> b) ->
  tr1:trace_ a -> tr2:trace_ a ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures (fmap_trace f tr1) <$ (fmap_trace f tr2))
  [SMTPat (fmap_trace f tr1);
   SMTPat (fmap_trace f tr2);
   SMTPat (tr1 <$ tr2)
  ]
let fmap_trace_later #a #b f tr1 tr2 =
  reveal_opaque (`%grows) (grows #a);
  reveal_opaque (`%grows) (grows #b);
  fmap_trace_prefix f tr2 (trace_length tr1)

val fmap_trace_recover_before:
  #a:Type -> #b:Type ->
  f:(a -> b) ->
  tr1:trace_ b -> tr2:trace_ a ->
  Pure (trace_ a)
  (requires
    tr1 <$ fmap_trace f tr2
  )
  (ensures fun tr1' ->
    tr1 == fmap_trace f tr1' /\
    tr1' <$ tr2
  )
let fmap_trace_recover_before #a #b f tr1 tr2 =
  reveal_opaque (`%grows) (grows #b);
  fmap_trace_prefix f tr2 (trace_length tr1);
  prefix tr2 (trace_length tr1)

val get_entry_at_fmap_trace:
  #a:Type -> #b:Type ->
  f:(a -> b) -> tr:trace_ a -> i:timestamp{i `on_trace` tr} ->
  Lemma (
    get_entry_at (fmap_trace f tr) i == fmap_trace_entry f (get_entry_at tr i)
  )
let rec get_entry_at_fmap_trace #a #b f tr i =
  if i+1 = trace_length tr then ()
  else get_entry_at_fmap_trace f (init tr) i

val entry_at_fmap_trace:
  #a:Type -> #b:Type ->
  f:(a -> b) -> tr:trace_ a -> i:timestamp -> entry:trace_entry_ a ->
  Lemma
  (requires entry_at tr i entry)
  (ensures entry_at (fmap_trace f tr) i (fmap_trace_entry f entry))
let entry_at_fmap_trace #a #b f tr i entry =
  if i >= trace_length tr then ()
  else (
    get_entry_at_fmap_trace f tr i
  )

val entry_at_fmap_trace_eq:
  #a:Type -> #b:Type ->
  f:(a -> b) -> tr:trace_ a -> i:timestamp -> entry:trace_entry_ a ->
  Lemma
  (requires ~(RandGen? entry))
  (ensures entry_at tr i entry <==> entry_at (fmap_trace f tr) i (fmap_trace_entry f entry))
let entry_at_fmap_trace_eq #a #b f tr i entry =
  if i >= trace_length tr then ()
  else (
    get_entry_at_fmap_trace f tr i
  )

val entry_exists_fmap_trace:
  #a:Type -> #b:Type ->
  f:(a -> b) -> tr:trace_ a -> entry:trace_entry_ a ->
  Lemma
  (requires entry_exists tr entry)
  (ensures entry_exists (fmap_trace f tr) (fmap_trace_entry f entry))
let entry_exists_fmap_trace #a #b f tr entry =
  eliminate exists i. entry_at tr i entry
  returns entry_exists (fmap_trace f tr) (fmap_trace_entry f entry)
  with _. (
    entry_at_fmap_trace f tr i entry
  )

val entry_exists_fmap_trace_eq:
  #a:Type -> #b:Type ->
  f:(a -> b) -> tr:trace_ a -> entry:trace_entry_ a ->
  Lemma
  (requires ~(RandGen? entry))
  (ensures entry_exists tr entry <==> entry_exists (fmap_trace f tr) (fmap_trace_entry f entry))
let entry_exists_fmap_trace_eq #a #b f tr entry =
  introduce forall i. entry_at tr i entry <==> entry_at (fmap_trace f tr) i (fmap_trace_entry f entry) with (
    entry_at_fmap_trace_eq f tr i entry
  )

val replace_label:
  #a:Type -> #b:Type ->
  b ->
  a -> b
let replace_label #a #b x _ = x

val forget_label:
  #a:Type ->
  a -> unit
let forget_label #a = replace_label ()

val trace_forget_labels:
  trace ->
  trace_ unit
let trace_forget_labels tr =
  fmap_trace forget_label tr


(*** Trace Searching ***)

#push-options "--fuel 2 --ifuel 1"
/// Finds the first (oldest) trace entry satisfying a given predicate.
[@@"opaque_to_smt"]
val trace_search_first: #label_t:Type -> tr:trace_ label_t -> p:(trace_entry_ label_t -> bool) ->
    Pure (option timestamp)
    (requires True)
    (ensures fun ts_opt ->
       match ts_opt with
       | None -> forall ts. ts `on_trace` tr ==> ~(p(get_entry_at tr ts))
       | Some ts -> (
         ts `on_trace` tr /\
         p (get_entry_at tr ts) /\
         forall ts'. (ts' `on_trace` tr /\ p (get_entry_at tr ts')) ==> ts' >= ts
       )
    )
let rec trace_search_first tr p
  = match tr with
    | Nil -> None
    | Snoc hd entry ->
      match trace_search_first hd p with
      | None -> if p entry then Some (last_timestamp tr) else None
      | Some ts -> Some ts

/// Finds the last (most recent) trace entry satisfying a given predicate.
[@@"opaque_to_smt"]
val trace_search_last: #label_t:Type -> tr:trace_ label_t -> p:(trace_entry_ label_t -> bool) ->
    Pure (option timestamp)
    (requires True)
    (ensures fun ts_opt ->
       match ts_opt with
       | None -> forall ts. ts `on_trace` tr ==> ~(p(get_entry_at tr ts))
       | Some ts -> (
         ts `on_trace` tr /\
         p (get_entry_at tr ts) /\
         forall ts'. (ts' `on_trace` tr /\ p (get_entry_at tr ts')) ==> ts' <= ts
       )
    )
let rec trace_search_last tr p
  = match tr with
    | Nil -> None
    | Snoc hd entry ->
      if p entry then
        Some (last_timestamp tr)
      else
        trace_search_last hd p
#pop-options

/// When searching the trace for an entry that we know to exist, we need to be able
/// to decide if a given entry is the one we are looking for, and so we use this
/// label-ignoring equivalence. This is exactly == for non-RandGen trace entries,
/// but treats two RandGen entries with the same non-label content as equivalent.
let trace_entry_equiv (#label_t:Type) (e1 e2:trace_entry_ label_t)
  : bool
  = (fmap_trace_entry forget_label e1) = (fmap_trace_entry forget_label e2)

/// The trace_find functions make use of trace_search to get the timestamp of a
/// trace entry that is already known to exist on the trace. Since a given entry
/// may in principle occur multiple times, we have two functions to give the first
/// and last occurrence of such an entry.
[@@"opaque_to_smt"]
val trace_find_first: #label_t:Type -> tr:trace_ label_t -> e:trace_entry_ label_t{entry_exists tr e} ->
    Pure timestamp
      (requires True)
      (ensures fun ts ->
        ts `on_trace` tr /\
        trace_entry_equiv e (get_entry_at tr ts) /\
        forall ts'. (ts' `on_trace` tr /\ trace_entry_equiv e (get_entry_at tr ts')) ==> ts' >= ts
      )
let trace_find_first tr e
  = Some?.v (trace_search_first tr (trace_entry_equiv e))

[@@"opaque_to_smt"]
val trace_find_last: #label_t:Type -> tr:trace_ label_t -> e:trace_entry_ label_t{entry_exists tr e} ->
    Pure timestamp
      (requires True)
      (ensures fun ts ->
        ts `on_trace` tr /\
        trace_entry_equiv e (get_entry_at tr ts) /\
        forall ts'. (ts' `on_trace` tr /\ trace_entry_equiv e (get_entry_at tr ts')) ==> ts' <= ts
      )
let trace_find_last tr e
  = Some?.v (trace_search_last tr (trace_entry_equiv e))
