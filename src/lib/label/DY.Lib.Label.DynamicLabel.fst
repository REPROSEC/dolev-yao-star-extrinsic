module DY.Lib.Label.DynamicLabel

open DY.Core
open DY.Lib.Label.Event
open DY.Lib.Label.BigJoin

open DY.Lib.Label.DynamicLabelEvent


(*** Reveal event triggered label ***)

val reveal_event_label : timestamp -> principal -> principal -> label
let reveal_event_label ts revealed_to prin = event_triggered_label prin {to=revealed_to; point=ts;}

val reveal_event_triggered_label :
  timestamp -> principal -> label
let reveal_event_triggered_label ts revealed_to = big_join (reveal_event_label ts revealed_to)

#push-options "--fuel 0 --ifuel 1"
val is_corrupt_reveal_event_triggered_label:
  tr:trace ->
  ts:timestamp -> revealed_to:principal ->
  Lemma (
    is_corrupt tr (reveal_event_triggered_label ts revealed_to)
    <==>
    exists prin. reveal_event_triggered tr prin revealed_to ts
  )
  [SMTPat (is_corrupt tr (reveal_event_triggered_label ts revealed_to))]
let is_corrupt_reveal_event_triggered_label tr ts revealed_to =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at)
#pop-options

(*** Reveal principal label ***)


val reveal_principal_label_meet :
  timestamp ->
  principal -> label
let reveal_principal_label_meet ts = fun prin -> meet (principal_label prin) (reveal_event_triggered_label ts prin)

// this label is corrupt if reveal_event is triggered then the principal_label is corrupt
val reveal_principal_label :
  timestamp ->
  label
let reveal_principal_label ts = big_join (reveal_principal_label_meet ts)

val reveal_principal_label_can_flow_to_principal_label :
  tr:trace ->
  prin:principal ->
  revealed_to:principal ->
  ts:timestamp ->
  Lemma
  (requires reveal_event_triggered tr prin revealed_to ts)
  (ensures (
    reveal_principal_label ts `can_flow tr` (principal_label revealed_to)
  ))
let reveal_principal_label_can_flow_to_principal_label tr revealer revealed_to ts =
  is_corrupt_reveal_event_triggered_label tr ts revealed_to;
  big_join_flow_to_component tr (reveal_principal_label_meet ts) revealed_to;
  assert(reveal_event_triggered_label ts revealed_to `can_flow tr` public)

val is_corrupt_reveal_principal_label :
  tr:trace ->
  ts:timestamp ->
  Lemma (
    is_corrupt tr (reveal_principal_label ts)
    <==>
    exists prin revealed_to. reveal_event_triggered tr prin revealed_to ts /\ is_corrupt tr (principal_label revealed_to)
  )

let is_corrupt_reveal_principal_label tr ts =
  ()

// not sure if this is useful, can't see how you can enforce this forall clause.
val certain_corruption :
  {| pi: protocol_invariants |} ->
  {| cusages: crypto_usages |} ->
  tr:trace ->
  generator:principal ->
  issued_to:principal ->
  secret:bytes{Rand? secret} ->
  ts:timestamp{Rand?.time secret = ts} ->
  Lemma
  (requires
    trace_invariant tr /\
    is_secret (reveal_principal_label ts) tr secret /\
    reveal_event_triggered tr generator generator ts /\
    reveal_event_triggered tr generator issued_to ts /\
    (forall p1 p2. reveal_event_triggered tr p1 p2 ts ==> 
      p1 == generator /\ (p2 == generator \/ p2 == issued_to)
    ) /\
    attacker_knows tr secret 
  )
  (ensures 
    is_corrupt tr (principal_label generator) \/ 
    is_corrupt tr (principal_label issued_to)
  )
let certain_corruption #cu tr generator issued_to secret ts =
  attacker_only_knows_publishable_values tr secret;
  ()

// this is a function to produce a nonce with a dynamic label with an initial reveal to the generator of the nonce
[@@ "opaque_to_smt"]
val mk_rand_dynamic_label :
  usg:usage -> len:nat{len <> 0} -> generator:principal ->
  traceful bytes
let mk_rand_dynamic_label usg len generator =
  let* time = get_time in
  add_entry (RandGen usg (reveal_principal_label time) len);*
  trigger_reveal_event generator generator time;* 
  return (Rand len time)
