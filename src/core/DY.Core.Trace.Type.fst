module DY.Core.Trace.Type

open DY.Core.List
open DY.Core.Bytes.Type
open DY.Core.Label.Type

/// This module defines the trace type, and simple predicates on it.
/// It is separated from functions and predicates on trace (manipulation, invariants)
/// in order to avoid dependency cycles.
///
/// The trace is a log of every event that has happened during a protocol execution,
/// such as messages sent on the network, state storage or corruption by the attacker,
/// as is standard is symbolic analysis tools to express security properties.
///
/// Given a trace, we can for example deduce:
/// - what bytestrings are known by the attacker (see DY.Core.Attacker.Knowledge.attacker_knows),
/// - what principals are corrupt (see DY.Core.Label.is_corrupt),
/// - what protocol steps have been reached by some principals,
/// - and more!
///
/// In turn, the set of traces that are reachable by executions of the protocol
/// can be used to express security properties.
/// For example, confidentiality can often be expressed as:
///   in every trace resulting from an execution of the protocol,
///   if the attacker knows some secret key,
///   then it must have corrupt some principal.
/// As another example, authentication can often be expressed as:
///   in every trace resulting from an execution of the protocol,
///   if Alice has finished a handshake with Bob,
///   then Bob must have initiated a handshake with Alice.


/// The type for events in the trace.

type trace_event =
  // A message has been sent on the network.
  | MsgSent: bytes -> trace_event
  // A random number has been generated, with some usage and label.
  | RandGen: usg:usage -> lab:label -> len:nat{len <> 0} -> trace_event
  // A state of a principal has been corrupt.
  | Corrupt: prin:principal -> sess_id:state_id -> trace_event
  // A principal stored some state.
  | SetState: prin:principal -> sess_id:state_id -> content:bytes -> trace_event
  // A custom and protocol-specific event has been triggered by a principal.
  | Event: prin:principal -> tag:string -> content:bytes -> trace_event


type trace = rev_list trace_event

/// The length of a trace.

val length: trace -> nat
let rec length tr =
  match tr with
  | Nil -> 0
  | Snoc init last -> length init + 1

/// a type macro for timestamps (indices on the trace)

type timestamp = nat

(*** Prefix and trace extension ***)

/// Compute the prefix of a trace.

[@@ "opaque_to_smt"]
val prefix: tr:trace -> i:timestamp{i <= length tr} -> trace
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
val grows: trace -> trace -> prop
let grows tr1 tr2 =
  length tr1 <= length tr2 /\
  tr1 == prefix tr2 (length tr1)

/// It is used a lot in DY*, therefore we define an operator shorthand.

let (<$) = grows

/// The relation <$ is reflexive.

val grows_reflexive:
  tr:trace ->
  Lemma (tr <$ tr)
  [SMTPat (tr <$ tr)]
let grows_reflexive tr =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix)

/// The relation <$ is transitive.

val grows_transitive:
  tr1:trace -> tr2:trace -> tr3:trace ->
  Lemma
  (requires tr1 <$ tr2 /\ tr2 <$ tr3)
  (ensures tr1 <$ tr3)
  [SMTPat (tr1 <$ tr2); SMTPat (tr1 <$ tr3)]
let rec grows_transitive tr1 tr2 tr3 =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
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
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
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
  reveal_opaque (`%grows) (grows)

/// The prefix function outputs traces that are prefixes of the input.

val prefix_grows:
  tr:trace -> i:timestamp{i <= length tr} ->
  Lemma
  (ensures (prefix tr i) <$ tr)
  //TODO: is this SMTPat dangerous? Should we restrict it to the "safe" on below?
  [SMTPat (prefix tr i)]
  //[SMTPat ((prefix tr i) <$ tr)]
let prefix_grows tr i =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix)

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
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
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
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  if length tr1 = length tr2 then ()
  else (
    let Snoc tr2_init _ = tr2 in
    prefix_prefix_eq tr1 tr2_init i
  )



val init_is_prefix:
  tr:trace{Snoc? tr} ->
  Lemma 
  (let Snoc init _ = tr in
    init <$ tr
  )
let init_is_prefix tr =
    reveal_opaque (`%grows) (grows);
    norm_spec [zeta; delta_only [`%prefix]] (prefix)

let nil_grows (tr:trace):
  Lemma (Nil <$ tr)
  [SMTPat (Nil <$ tr)]
  = reveal_opaque (`%grows) grows


/// concatenation of traces  
let rec trace_concat tr1 tr2 =
  match tr2 with
  | Nil -> tr1
  | Snoc init2 ev2 ->
      Snoc (trace_concat tr1 init2) ev2
      
/// the first part of the concat is a prefix of the result
val trace_concat_grows:
  tr1:trace -> tr2:trace ->
  Lemma (tr1 <$ trace_concat tr1 tr2)
//  [SMTPat (trace_concat tr1 tr2)]
let rec trace_concat_grows tr1 tr2 =
    reveal_opaque (`%grows) (grows);
    norm_spec [zeta; delta_only [`%prefix]] (prefix);
    match tr2 with
    | Nil -> ()
    | Snoc init ev -> 
           trace_concat_grows tr1 init

val trace_concat_nil:
  tr:trace ->
  Lemma (tr `trace_concat` Nil = tr)
  [SMTPat (tr `trace_concat` Nil)]
let trace_concat_nil tr = ()

(*** Event in the trace predicates ***)

/// Retrieve the event at some timestamp in the trace.

val get_event_at: tr:trace -> i:timestamp{i < length tr} -> trace_event
let rec get_event_at tr i =
  if i+1 = length tr then
    let Snoc _ last = tr in
    last
  else (
    let Snoc tr_init _ = tr in
    get_event_at tr_init i
  )



/// Has some particular event been triggered at a some particular timestamp in the trace?

val event_at: trace -> timestamp -> trace_event -> prop
let event_at tr i e =
  if i >= length tr then
    False
  else
    e == get_event_at tr i

/// Has some particular event been triggered in the trace (at any timestamp)?

val event_exists: trace -> trace_event -> prop
let event_exists tr e =
  exists i. event_at tr i e


/// The property that there are no state entries
/// for the principal and a particular session

val no_set_state_entry_for:
  principal -> state_id -> trace -> prop
let no_set_state_entry_for p sid tr = 
  forall (ts:timestamp{ts < length tr}).
    match get_event_at tr ts with
    | SetState p' sid' _ -> p' <> p \/ sid' <> sid
    | _ -> True

/// An event in the trace stays here when the trace grows.

val event_at_grows:
  tr1:trace -> tr2:trace ->
  i:timestamp -> e:trace_event ->
  Lemma
  (requires event_at tr1 i e /\ tr1 <$ tr2)
  (ensures event_at tr2 i e)
  [SMTPat (event_at tr1 i e); SMTPat (tr1 <$ tr2)]
let rec event_at_grows tr1 tr2 i e =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  if i >= length tr1 then ()
  else if length tr1 >= length tr2 then ()
  else (
    let Snoc tr2_init _ = tr2 in
    event_at_grows tr1 tr2_init i e
  )


let last_event_exists (tr:trace):
  Lemma
  (requires Snoc? tr
  )
  (ensures (
     let Snoc _ ev = tr in
     event_exists tr ev
     )
  )
  [SMTPat (Snoc? tr)]
  = let Snoc _ ev = tr in
    assert(event_at tr (length tr - 1) ev)

/// given an event on a trace, we often need the trace up until right before that entry

val prefix_before_event:
  tr:trace -> ev:trace_event{event_exists tr ev} -> trace
let rec prefix_before_event tr the_ev =
  match tr with
  | Snoc init ev ->
      if ev = the_ev 
        then init
        else init `prefix_before_event` the_ev
        
val prefix_before_event_is_prefix:
  tr:trace -> ev:trace_event{event_exists tr ev} -> 
  Lemma ((tr `prefix_before_event` ev) <$ tr)
  [SMTPat (tr `prefix_before_event` ev)]
let rec prefix_before_event_is_prefix tr the_ev =
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr with
  | Nil -> ()
  | Snoc init ev ->
         if ev = the_ev
           then ()
           else
             prefix_before_event_is_prefix init the_ev


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

val was_corrupt: trace -> principal -> state_id -> prop
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
  | Rand usg lab len time ->
    time == i /\ event_at tr i (RandGen usg lab len)
  | _ -> False
