module DY.Lib.Label.DynamicGeneralLabel

open DY.Core
open DY.Lib.Label.Event
open DY.Lib.Label.BigJoin

open DY.Lib.Label.DynamicGeneralLabelEvent


(*** Reveal event triggered label ***)

val reveal_general_event_label : timestamp -> bytes -> principal -> label
let reveal_general_event_label ts new_label_bytes prin = event_triggered_label prin {new_label=new_label_bytes; point=ts;}

val reveal_general_event_triggered_label :
  timestamp -> bytes -> label
let reveal_general_event_triggered_label ts new_label_bytes = big_join (reveal_general_event_label ts new_label_bytes)

#push-options "--fuel 0 --ifuel 1"
val is_corrupt_reveal_general_event_triggered_label:
  tr:trace ->
  ts:timestamp -> new_label_bytes:bytes ->
  Lemma (
    is_corrupt tr (reveal_general_event_triggered_label ts new_label_bytes)
    <==>
    exists prin. reveal_general_event_triggered tr prin new_label_bytes ts
  )
  [SMTPat (is_corrupt tr (reveal_general_event_triggered_label ts new_label_bytes))]
let is_corrupt_reveal_general_event_triggered_label tr ts revealed_to =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%reveal_general_event_triggered_at) (reveal_general_event_triggered_at)
#pop-options

(*** Reveal principal label ***)

// constructs a parameterised label that is corrupt when the label of the parameterised bytes is corrupt and an event exists to record that these exact bytes have been revealed to.
val reveal_general_label_meet :
  {|crypto_usages|} -> tr:trace -> timestamp ->
  b:bytes -> label
let reveal_general_label_meet #cu tr ts = fun new_bytes -> meet (get_label #cu tr new_bytes) (reveal_general_event_triggered_label ts new_bytes)

// this label is corrupt if reveal_event is triggered then the original label is corrupt
val reveal_general_label :
  {|crypto_usages|} -> trace -> timestamp ->
  label
let reveal_general_label #cu tr ts =
  // type #a of the big_join is (b:bytes{bytes_well_formed tr b})
  big_join (reveal_general_label_meet #cu tr ts)

val reveal_general_label_meet_later :
  {|crypto_usages|} ->
  tr1 : trace -> tr2 : trace ->
  i:timestamp -> b:bytes ->
  Lemma
  (requires tr1 <$ tr2 /\ bytes_well_formed tr1 b)
  (ensures (
    reveal_general_label_meet tr1 i b == reveal_general_label_meet tr2 i b
  ))
let reveal_general_label_meet_later #cu tr1 tr2 i b = ()

val reveal_general_label_meet_later' :
  {|crypto_usages|} ->
  tr1 : trace -> tr2 : trace -> i:timestamp ->
  b:bytes{bytes_well_formed tr1 b} ->
  Lemma
  (ensures (
    tr1 <$ tr2 ==>
    reveal_general_label_meet tr1 i b == reveal_general_label_meet tr2 i b
  ))
let reveal_general_label_meet_later' #cu tr1 tr2 i b = ()

val is_corrupt_general_label_meet :
  {|crypto_usages|} ->
  tr1 : trace -> tr2 : trace ->
  i:timestamp ->
  b:bytes{bytes_well_formed tr1 b} ->
  Lemma(
    tr1 <$ tr2 ==>
    (is_corrupt tr2 (reveal_general_label_meet tr1 i b) <==> is_corrupt tr2 (reveal_general_label_meet tr2 i b))
  )
let is_corrupt_general_label_meet #cu tr1 tr2 i b = ()

val is_eq_general_label_meet :
 {|crypto_usages|} ->
 tr1 : trace -> tr2 : trace ->
 i:timestamp ->
 b:bytes{bytes_well_formed tr1 b} ->
 Lemma(
   tr1 <$ tr2 ==>
   reveal_general_label_meet tr1 i b == reveal_general_label_meet tr2 i b
 )
let is_eq_general_label_meet #cu tr1 tr2 i b = ()

val big_join_equal_label_is_equal :
  #a:Type ->
  f1:(a -> label) -> f2:(a -> label) ->
  Lemma
  (requires (forall a. f1 a == f2 a))
  (ensures (big_join f1 == big_join f2))
let big_join_equal_label_is_equal f1 f2 =
  let temp (tr:trace) : Lemma(is_corrupt tr (big_join f1) <==> is_corrupt tr (big_join f2)) = () in
  intro_label_equal (big_join f1) (big_join f2) temp


// val is_corrupt_general_label_later :
//   {|crypto_usages|} ->
//   tr1 : trace -> tr2 : trace ->
//   i:timestamp ->
//   Lemma
//   (requires tr1 <$ tr2)
//   (ensures (
//     is_corrupt tr2 (big_join (reveal_general_label_meet tr1 i)) ==> is_corrupt tr2 (big_join (reveal_general_label_meet tr2 i))
//   ))
// let is_corrupt_general_label_later #cu tr1 tr2 i =
//   let f1 = reveal_general_label_meet tr1 i in
//   let f2 = reveal_general_label_meet tr2 i in
//   assert(forall a. f1 a == f2 a)


// val reveal_general_label_later :
//   {|crypto_usages|} ->
//   tr1 : trace -> tr2 : trace ->
//   i:timestamp ->
//   Lemma
//   (requires tr1 <$ tr2)
//   (ensures (
//     big_join (reveal_general_label_meet tr1 i) == big_join (reveal_general_label_meet tr2 i)
//   ))
// let reveal_general_label_later #cu tr1 tr2 i =
//   let f1 = reveal_general_label_meet tr1 i in
//   let f2 = reveal_general_label_meet tr2 i in
//   assert(forall b. f1 b == f2 b);
//   let temp tr : Lemma(is_corrupt tr (big_join f1) ==> is_corrupt tr (big_join f2)) = () in
//   big_join_equal_label_is_equal f1 f2 ;
//   assert(big_join f1 == big_join f2)

////  need a lemma exposing the trace growing retains corruption of the label.
// val general_label_later :
//   {| crypto_usages |} ->
//   tr1 : trace -> tr2 : trace ->
//   b : bytes ->
//   i : timestamp ->
//   Lemma
//     (requires (
//       tr1 <$ tr2
//     ))
//     (ensures (is_corrupt tr2 (reveal_general_label tr1 i) ==> is_corrupt tr2 (reveal_general_label tr2 i)))
// let general_label_later #cu tr1 tr2 b i =
//   is_corrupt_general_label_later tr1 tr2 i

val reveal_general_label_can_flow_to_general_label :
  {| crypto_usages |} -> tr:trace ->
  old_tr:trace{old_tr <$ tr} ->
  prin:principal ->
  new_label_bytes:bytes ->
  ts:timestamp ->
  Lemma
  (requires (
    reveal_general_event_triggered tr prin new_label_bytes ts /\
    bytes_well_formed old_tr new_label_bytes
  ))
  (ensures (
    reveal_general_label old_tr ts `can_flow tr` (get_label tr new_label_bytes)
  ))
let reveal_general_label_can_flow_to_general_label #cu tr old_tr revealer new_label_bytes ts =
  is_corrupt_reveal_general_event_triggered_label tr ts new_label_bytes;
  big_join_flow_to_component tr (reveal_general_label_meet old_tr ts) new_label_bytes;
  assert(reveal_general_event_triggered_label ts new_label_bytes `can_flow tr` public)

val is_corrupt_reveal_general_label :
  {| crypto_usages |} -> tr:trace ->
  ts:timestamp ->
  Lemma (
    is_corrupt tr (reveal_general_label tr ts)
    <==>
    exists prin new_label_bytes. reveal_general_event_triggered tr prin new_label_bytes ts /\ is_corrupt tr (get_label tr new_label_bytes)
  )
let is_corrupt_reveal_general_label tr ts =
  ()


// this is a function to produce a nonce with a dynamic label with an initial reveal to the generator of the nonce
// [@@ "opaque_to_smt"]
// val mk_rand_dynamic_general_label :
//   usg:usage -> len:nat{len <> 0} -> generator:principal ->
//   traceful bytes
// let mk_rand_dynamic_label usg len generator =
//   let* time = get_time in
//   add_entry (RandGen usg (reveal_principal_label time) len);*
//   trigger_reveal_event generator generator time;*
//   return (Rand len time)
