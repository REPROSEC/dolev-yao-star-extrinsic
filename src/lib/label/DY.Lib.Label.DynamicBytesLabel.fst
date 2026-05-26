module DY.Lib.Label.DynamicBytesLabel

open DY.Core
open DY.Lib.Event.Typed
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

val is_corrupt_reveal_to_bytes_label :
  {| crypto_usages |} ->
  tr:trace ->
  label_tr:trace ->
  ts:timestamp ->
  Lemma (
    is_corrupt tr (reveal_to_bytes_label label_tr ts)
    <==>
    exists prin new_bytes.
      reveal_to_bytes_label_event_triggered tr prin new_bytes ts /\
      is_corrupt tr (get_label label_tr new_bytes)
  )
  [SMTPat (is_corrupt tr (reveal_to_bytes_label label_tr ts))]
let is_corrupt_reveal_to_bytes_label #cu tr label_tr ts =
  is_corrupt_big_join tr (reveal_to_bytes_label_meet label_tr ts);
  introduce forall new_bytes.
    is_corrupt tr (reveal_to_bytes_label_meet label_tr ts new_bytes) <==>
      (exists prin.
        reveal_to_bytes_label_event_triggered tr prin new_bytes ts /\
        is_corrupt tr (get_label label_tr new_bytes))
  with (
    is_corrupt_meet tr (get_label label_tr new_bytes) (reveal_to_bytes_label_event_triggered_label ts new_bytes);
    is_corrupt_reveal_to_bytes_label_event_triggered_label tr ts new_bytes
  )

val reveal_to_bytes_label_event_bytes_well_formed_later :
  tr1:trace ->
  tr2:trace ->
  ts:timestamp ->
  prop
let reveal_to_bytes_label_event_bytes_well_formed_later tr1 tr2 ts =
  forall tr_extended prin new_bytes.
    tr2 <$ tr_extended /\
    reveal_to_bytes_label_event_triggered tr_extended prin new_bytes ts ==>
    bytes_well_formed tr1 new_bytes

val reveal_to_bytes_label_equivalent_later :
  {| crypto_usages |} ->
  tr1:trace ->
  tr2:trace ->
  ts:timestamp ->
  Lemma
  (requires (
    tr1 <$ tr2 /\
    reveal_to_bytes_label_event_bytes_well_formed_later tr1 tr2 ts
  ))
  (ensures (
    reveal_to_bytes_label tr1 ts `equivalent tr2` reveal_to_bytes_label tr2 ts
  ))
let reveal_to_bytes_label_equivalent_later #cu tr1 tr2 ts =
  intro_equivalent tr2 (reveal_to_bytes_label tr1 ts) (reveal_to_bytes_label tr2 ts) (fun tr_extended ->
    is_corrupt_reveal_to_bytes_label tr_extended tr1 ts;
    is_corrupt_reveal_to_bytes_label tr_extended tr2 ts;
    introduce forall prin new_bytes.
      reveal_to_bytes_label_event_triggered tr_extended prin new_bytes ts ==>
      get_label tr1 new_bytes == get_label tr2 new_bytes
    with (
      introduce _ ==> _ with _. (
        get_label_later tr1 tr2 new_bytes
      )
    )
  )

val reveal_to_bytes_label_can_flow_later :
  {| crypto_usages |} ->
  tr1:trace ->
  tr2:trace ->
  ts:timestamp ->
  Lemma
  (requires (
    tr1 <$ tr2 /\
    reveal_to_bytes_label_event_bytes_well_formed_later tr1 tr2 ts
  ))
  (ensures (
    reveal_to_bytes_label tr1 ts `can_flow tr2` reveal_to_bytes_label tr2 ts
  ))
let reveal_to_bytes_label_can_flow_later #cu tr1 tr2 ts =
  reveal_to_bytes_label_equivalent_later tr1 tr2 ts

val reveal_to_bytes_label_later_can_flow_to_earlier :
  {| crypto_usages |} ->
  tr1:trace ->
  tr2:trace ->
  ts:timestamp ->
  Lemma
  (requires (
    tr1 <$ tr2 /\
    reveal_to_bytes_label_event_bytes_well_formed_later tr1 tr2 ts
  ))
  (ensures (
    reveal_to_bytes_label tr2 ts `can_flow tr2` reveal_to_bytes_label tr1 ts
  ))
let reveal_to_bytes_label_later_can_flow_to_earlier #cu tr1 tr2 ts =
  reveal_to_bytes_label_equivalent_later tr1 tr2 ts

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

// The reveal_to_bytes label snapshot taken at timestamp `ts` of `tr`.
val reveal_to_bytes_label_at_time :
  {| crypto_usages |} -> tr:trace -> ts:timestamp{ts <= trace_length tr} ->
  label
let reveal_to_bytes_label_at_time #cu tr ts =
  reveal_to_bytes_label (prefix tr ts) ts

// High-level corruption lemma for [reveal_to_bytes_label_at_time].
// Given a reveal_event predicate (i.e. `has_event_pred reveal_event_pred.pred`), the snapshot label is
// corrupt iff a reveal event for some `key` has been triggered for `ts` and
// `key` itself is corrupt under the **current** trace.
val is_corrupt_reveal_to_bytes_label_at_time :
  {| protocol_invariants |} ->
  reveal_event_pred:reveal_to_bytes_label_event_predicate ->
  tr:trace -> ts:timestamp ->
  Lemma
  (requires (
    trace_invariant tr /\
    ts <= trace_length tr /\
    has_event_pred reveal_event_pred.pred
  ))
  (ensures (
    is_corrupt tr (reveal_to_bytes_label_at_time tr ts)
    <==>
    (exists prin key.
      reveal_to_bytes_label_event_triggered tr prin key ts /\
      is_corrupt tr (get_label tr key))
  ))
let is_corrupt_reveal_to_bytes_label_at_time #invs reveal_event_pred tr ts =
  introduce forall prin key.
    reveal_to_bytes_label_event_triggered tr prin key ts ==>
      (is_corrupt tr (get_label (prefix tr ts) key)
        <==> is_corrupt tr (get_label tr key))
  with (
    introduce _ ==> _ with _. (
      eliminate exists i. reveal_to_bytes_label_event_triggered_at tr i prin key ts
      returns
        (is_corrupt tr (get_label (prefix tr ts) key)
          <==> is_corrupt tr (get_label tr key))
      with _. (
        reveal_opaque (`%reveal_to_bytes_label_event_triggered_at)
                      (reveal_to_bytes_label_event_triggered_at);
        event_triggered_at_implies_pred reveal_event_pred.pred tr i prin
          { bytes_label = key; point = ts };
        reveal_event_pred.pred_knowable (prefix tr i) prin
          { bytes_label = key; point = ts };
        get_label_later (prefix tr ts) tr key
      )
    )
  )
