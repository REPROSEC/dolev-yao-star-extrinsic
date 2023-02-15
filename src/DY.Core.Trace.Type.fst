module DY.Core.Trace.Type

open DY.Core.Bytes.Type
open DY.Core.Label.Type

type trace_event =
  | MsgSent: bytes -> trace_event
  | RandGen: trace_event
  | Corrupt: who:pre_pre_label -> trace_event
  | SetState: p:principal -> s:nat -> content:bytes -> trace_event

type trace =
  | Nil: trace
  | Snoc: trace -> trace_event -> trace

val length: trace -> nat
let rec length tr =
  match tr with
  | Nil -> 0
  | Snoc init last -> length init + 1

val grows: trace -> trace -> prop
let rec grows tr1 tr2 =
  if length tr1 >= length tr2 then
    tr1 == tr2
  else
    let Snoc tr2_init _ = tr2 in
    grows tr1 tr2_init

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

//type stable_trace_pred =
//  pred:(trace -> prop){forall tr1 tr2. tr1 <$ tr2 /\ pred tr1 ==> pred tr2}
//
//val mk_stable_trace_pred:
//  pred:(trace -> prop) ->
//  pf:(tr1:trace -> tr2:trace -> Lemma (requires tr1 <$ tr2 /\ pred tr1) (ensures pred tr2)) ->
//  stable_trace_pred
//let mk_stable_trace_pred pred pf =
//  introduce forall tr1 tr2. tr1 <$ tr2 /\ pred tr1 ==> pred tr2 with (
//    introduce _ ==> _ with _. (
//      pf tr1 tr2
//    )
//  );
//  pred

val event_at: trace -> trace_event -> nat -> prop
let rec event_at tr e i =
  if i >= length tr then
    False
  else if i+1 = length tr then
    let Snoc _ last = tr in
    e == last
  else (
    assert(i < length tr); // Sanity check
    let Snoc init _ = tr in
    event_at init e i
  )

val event_exists: trace -> trace_event -> prop
let rec event_exists tr e =
  match tr with
  | Nil -> False
  | Snoc tr_init event_last ->
    event_exists tr_init e \/ e == event_last

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
  e:trace_event -> i:nat ->
  Lemma
  (requires event_at tr1 e i /\ tr1 <$ tr2)
  (ensures event_at tr2 e i)
  [SMTPat (event_at tr1 e i); SMTPat (tr1 <$ tr2)]
let rec event_at_grows tr1 tr2 e i =
  if i >= length tr1 then ()
  else if length tr1 >= length tr2 then ()
  else (
    let Snoc tr2_init _ = tr2 in
    event_at_grows tr1 tr2_init e i
  )

val event_exists_grows:
  tr1:trace -> tr2:trace ->
  e:trace_event ->
  Lemma
  (requires event_exists tr1 e /\ tr1 <$ tr2)
  (ensures event_exists tr2 e)
  [SMTPat (event_exists tr1 e); SMTPat (tr1 <$ tr2)]
let rec event_exists_grows tr1 tr2 e =
  if length tr1 >= length tr2 then ()
  else
    let Snoc tr2_init _ = tr2 in
    event_exists_grows tr1 tr2_init e



val msg_sent_on_network: trace -> bytes -> prop
let msg_sent_on_network tr msg =
  event_exists tr (MsgSent msg)
