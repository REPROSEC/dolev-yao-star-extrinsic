module DY.Core.Trace.Type

open DY.Core.Bytes.Type
open DY.Core.Label.Type

type trace_event =
  | MsgSent: bytes -> trace_event
  | RandGen: lab:label -> len:nat{len <> 0} -> trace_event
  | Corrupt: prin:principal -> sess_id:nat -> trace_event
  | SetState: prin:principal -> sess_id:nat -> content:bytes -> trace_event
  | Event: prin:principal -> tag:string -> content:bytes -> trace_event

type trace =
  | Nil: trace
  | Snoc: trace -> trace_event -> trace

val length: trace -> nat
let rec length tr =
  match tr with
  | Nil -> 0
  | Snoc init last -> length init + 1

val prefix: tr:trace -> i:nat{i <= length tr} -> trace
let rec prefix tr i =
  if length tr = i then
    tr
  else
    let Snoc tr_init _ = tr in
    prefix tr_init i

val grows: trace -> trace -> prop
let grows tr1 tr2 =
  length tr1 <= length tr2 /\
  tr1 == prefix tr2 (length tr1)

let (<$) = grows

val grows_transitive:
  tr1:trace -> tr2:trace -> tr3:trace ->
  Lemma
  (requires tr1 <$ tr2 /\ tr2 <$ tr3)
  (ensures tr1 <$ tr3)
  [SMTPat (tr1 <$ tr2); SMTPat (tr1 <$ tr3)]
let rec grows_transitive tr1 tr2 tr3 =
  if length tr2 >= length tr3 then
    ()
  else (
    let Snoc tr3_init _ = tr3 in
    grows_transitive tr1 tr2 tr3_init
  )

val length_prefix:
  tr:trace -> i:nat{i <= length tr} ->
  Lemma
  (ensures length (prefix tr i) == i)
  [SMTPat (length (prefix tr i))]
let rec length_prefix tr i =
  if length tr = i then ()
  else
    let Snoc tr_init _ = tr in
    length_prefix tr_init i

val prefix_grows:
  tr:trace -> i:nat{i <= length tr} ->
  Lemma
  (ensures (prefix tr i) <$ tr)
  //TODO: is this SMTPat dangerous? Should we restrict it to the "safe" on below?
  [SMTPat (prefix tr i)]
  //[SMTPat ((prefix tr i) <$ tr)]
let prefix_grows tr i = ()

val get_event_at: tr:trace -> i:nat{i < length tr} -> trace_event
let rec get_event_at tr i =
  if i+1 = length tr then
    let Snoc _ last = tr in
    last
  else (
    let Snoc tr_init _ = tr in
    get_event_at tr_init i
  )

val event_at: trace -> nat -> trace_event -> prop
let event_at tr i e =
  if i >= length tr then
    False
  else
    e == get_event_at tr i

val event_exists: trace -> trace_event -> prop
let event_exists tr e =
  exists i. event_at tr i e

val length_grows:
  tr1:trace -> tr2:trace ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures length tr1 <= length tr2)
  [SMTPat (tr1 <$ tr2)]
let rec length_grows tr1 tr2 =
  if length tr1 >= length tr2 then ()
  else (
    let Snoc tr2_init _ = tr2 in
    length_grows tr1 tr2_init
  )

val event_at_grows:
  tr1:trace -> tr2:trace ->
  i:nat -> e:trace_event ->
  Lemma
  (requires event_at tr1 i e /\ tr1 <$ tr2)
  (ensures event_at tr2 i e)
  [SMTPat (event_at tr1 i e); SMTPat (tr1 <$ tr2)]
let rec event_at_grows tr1 tr2 i e =
  if i >= length tr1 then ()
  else if length tr1 >= length tr2 then ()
  else (
    let Snoc tr2_init _ = tr2 in
    event_at_grows tr1 tr2_init i e
  )

val msg_sent_on_network: trace -> bytes -> prop
let msg_sent_on_network tr msg =
  event_exists tr (MsgSent msg)

val state_was_set: trace -> principal -> nat -> bytes -> prop
let state_was_set tr prin sess_id content =
  event_exists tr (SetState prin sess_id content)

val was_corrupt: trace -> principal -> nat -> prop
let was_corrupt tr prin sess_id =
  event_exists tr (Corrupt prin sess_id)

val event_triggered_at: trace -> nat -> principal -> string -> bytes -> prop
let event_triggered_at tr i prin tag content =
  event_at tr i (Event prin tag content)

val event_triggered: trace -> principal -> string -> bytes -> prop
let event_triggered tr prin tag content =
  exists i. event_triggered_at tr i prin tag content

val event_triggered_grows:
  tr1:trace -> tr2:trace ->
  prin:principal -> tag:string -> content:bytes  ->
  Lemma
  (requires event_triggered tr1 prin tag content /\ tr1 <$ tr2)
  (ensures event_triggered tr2 prin tag content)
  [SMTPat (event_triggered tr1 prin tag content); SMTPat (tr1 <$ tr2)]
let event_triggered_grows tr1 tr2 prin tag content = ()

val rand_generated_at: trace -> nat -> bytes -> prop
let rand_generated_at tr i b =
  match b with
  | Rand lab len time ->
    time == i /\ event_at tr i (RandGen lab len)
  | _ -> False
