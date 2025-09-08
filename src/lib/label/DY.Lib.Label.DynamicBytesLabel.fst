module DY.Lib.Label.DynamicBytesLabel

open DY.Core
open DY.Lib.Label.Event
open DY.Lib.Label.BigJoin

open DY.Lib.Label.DynamicBytesLabelEvent

(*** Reveal event triggered label ***)

val reveal_to_bytes_label_event_label : timestamp -> bytes -> principal -> label
let reveal_to_bytes_label_event_label ts new_label_bytes prin = event_triggered_label prin {bytes_label=new_label_bytes; point=ts;}

val reveal_to_bytes_label_event_triggered_label :
  timestamp -> bytes -> label
let reveal_to_bytes_label_event_triggered_label ts new_label_bytes = big_join (reveal_to_bytes_label_event_label ts new_label_bytes)

val is_corrupt_reveal_to_bytes_label_event_triggered_label:
  tr:trace ->
  ts:timestamp -> new_label_bytes:bytes ->
  Lemma (
    is_corrupt tr (reveal_to_bytes_label_event_triggered_label ts new_label_bytes)
    <==>
    exists prin. reveal_to_bytes_label_event_triggered tr prin new_label_bytes ts
  )
  [SMTPat (is_corrupt tr (reveal_to_bytes_label_event_triggered_label ts new_label_bytes))]
let is_corrupt_reveal_to_bytes_label_event_triggered_label tr ts revealed_to =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%reveal_to_bytes_label_event_triggered_at) (reveal_to_bytes_label_event_triggered_at)

(*** Reveal principal label ***)

// constructs a parameterised label that is corrupt when the label of the parameterised bytes is corrupt and an event exists to record that these exact bytes have been revealed to.
val reveal_to_bytes_label_meet :
  {|crypto_usages|} -> tr:trace -> timestamp ->
  b:bytes// {bytes_well_formed tr b}
  -> label
let reveal_to_bytes_label_meet #cu tr ts = fun new_bytes -> meet (get_label #cu tr new_bytes) (reveal_to_bytes_label_event_triggered_label ts new_bytes)

// this label is corrupt if reveal_event is triggered then the original label is corrupt
val reveal_to_bytes_label :
  {|crypto_usages|} -> trace -> timestamp ->
  label
let reveal_to_bytes_label #cu tr ts =
  big_join (reveal_to_bytes_label_meet #cu tr ts)


val reveal_to_bytes_label_can_flow_to_bytes_label :
  {| crypto_usages |} -> tr:trace ->
  old_tr:trace{old_tr <$ tr} ->
  prin:principal ->
  new_label_bytes:bytes ->
  ts:timestamp ->
  Lemma
  (requires (
    reveal_to_bytes_label_event_triggered tr prin new_label_bytes ts /\
    bytes_well_formed tr new_label_bytes
  ))
  (ensures (
    reveal_to_bytes_label old_tr ts `can_flow tr` (get_label old_tr new_label_bytes)
  ))
let reveal_to_bytes_label_can_flow_to_bytes_label #cu tr old_tr revealer new_label_bytes ts =
  is_corrupt_reveal_to_bytes_label_event_triggered_label tr ts new_label_bytes;
  big_join_flow_to_component tr (reveal_to_bytes_label_meet old_tr ts) new_label_bytes;
  assert(reveal_to_bytes_label_event_triggered_label ts new_label_bytes `can_flow tr` public)
