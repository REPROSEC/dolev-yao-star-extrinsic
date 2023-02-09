module DY.Trace.Invariant

open DY.Trace.Type
open DY.Bytes.Type
open DY.Bytes

val trace_invariant: protocol_preds -> trace -> prop
let rec trace_invariant preds tr =
  match tr with
  | Nil -> True
  | Snoc tr_init event ->
    trace_invariant preds tr_init /\ (
      match event with
      | MsgSent msg ->
        is_publishable preds tr msg
      | _ -> True
    )

val msg_sent_on_network_are_publishable:
  preds:protocol_preds -> tr:trace -> msg:bytes ->
  Lemma
  (requires
    trace_invariant preds tr /\
    msg_sent_on_network tr msg
  )
  (ensures is_publishable preds tr msg)
let rec msg_sent_on_network_are_publishable preds tr msg =
  match tr with
  | Nil -> assert(False)
  | Snoc tr_init (MsgSent msg') -> (
    assert(tr_init <$ tr);
    if msg = msg' then ()
    else (
      msg_sent_on_network_are_publishable preds tr_init msg
    )
  )
  | Snoc tr_init _ ->
    assert(tr_init <$ tr);
    msg_sent_on_network_are_publishable preds tr_init msg
