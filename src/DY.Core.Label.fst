module DY.Core.Label

open DY.Core.Label.Type
open DY.Core.Trace.Type

val pre_can_flow:
  pre_pre_label -> pre_pre_label -> prop
let pre_can_flow who1 who2 =
  who2 `pre_pre_label_order.rel` who1

val pre_can_flow_transitive:
  who1:pre_pre_label -> who2:pre_pre_label -> who3:pre_pre_label ->
  Lemma
  (requires who1 `pre_can_flow` who2 /\ who2 `pre_can_flow` who3)
  (ensures who1 `pre_can_flow` who3)
  [SMTPat (who1 `pre_can_flow` who2); SMTPat (who1 `pre_can_flow` who3)]
let pre_can_flow_transitive who1 who2 who3 =
  pre_pre_label_order.trans who3 who2 who1

val is_corrupt: trace -> pre_pre_label -> prop
let is_corrupt tr who =
  exists prin sess_id.
    who `pre_can_flow` (S prin sess_id) /\
    was_corrupt tr prin sess_id

val is_corrupt_later:
  tr1:trace -> tr2:trace ->
  who:pre_pre_label ->
  Lemma
  (requires is_corrupt tr1 who /\ tr1 <$ tr2)
  (ensures is_corrupt tr2 who)
  [SMTPat (is_corrupt tr1 who); SMTPat (tr1 <$ tr2)]
let is_corrupt_later tr1 tr2 who = ()

val is_corrupt_order:
  tr:trace ->
  who1:pre_pre_label -> who2:pre_pre_label ->
  Lemma
  (requires is_corrupt tr who1 /\ who2 `pre_can_flow` who1)
  (ensures is_corrupt tr who2)
  // TODO SMT pattern is weird, refactor
  [SMTPat (is_corrupt tr who1); SMTPat (who1 `pre_pre_label_order.rel` who2)]
let is_corrupt_order tr who1 who2 = ()

val can_flow: trace -> label -> label -> prop
let can_flow tr l1 l2 =
  l2 `(label_order (is_corrupt tr)).rel` l1

val secret: label
let secret =
  DY.Core.Label.Lattice.Leaf Secret

val public: label
let public =
  DY.Core.Label.Lattice.Leaf Public

val meet: label -> label -> label
let meet l1 l2 =
  DY.Core.Label.Lattice.Meet l1 l2

val join: label -> label -> label
let join l1 l2 =
  DY.Core.Label.Lattice.Join l1 l2

val principal_label: principal -> label
let principal_label prin =
  DY.Core.Label.Lattice.Leaf (State (P prin))

val principal_state_label: principal -> nat -> label
let principal_state_label prin sess_id =
  DY.Core.Label.Lattice.Leaf (State (S prin sess_id))

val can_flow_transitive:
  tr:trace -> l1:label -> l2:label -> l3:label ->
  Lemma
  (requires l1 `can_flow tr` l2 /\ l2 `can_flow tr` l3)
  (ensures l1 `can_flow tr` l3)
  [SMTPat (l1 `can_flow tr` l3); SMTPat (l1 `can_flow tr` l2)]
let can_flow_transitive tr l1 l2 l3 =
  (label_order (is_corrupt tr)).trans l3 l2 l1

val can_flow_later:
  tr1:trace -> tr2:trace ->
  l1:label -> l2:label ->
  Lemma
  (requires l1 `can_flow tr1` l2 /\ tr1 <$ tr2)
  (ensures l1 `can_flow tr2` l2)
  [SMTPat (l1 `can_flow tr1` l2); SMTPat (tr1 <$ tr2)]
let can_flow_later tr1 tr2 l1 l2 =
  DY.Core.Label.Lattice.lattice_order_monotone (pre_label_order pre_pre_label_order (is_corrupt tr1)) (pre_label_order pre_pre_label_order (is_corrupt tr2)) l2 l1

val secret_is_bottom:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` secret)
  [SMTPat (l `can_flow tr` secret)]
let secret_is_bottom tr l =
  DY.Core.Label.Lattice.bottom_to_bottom (pre_label_order pre_pre_label_order (is_corrupt tr)) Secret l

val public_is_top:
  tr:trace -> l:label ->
  Lemma
  (ensures public `can_flow tr` l)
  [SMTPat (public `can_flow tr` l)]
let public_is_top tr l =
  DY.Core.Label.Lattice.top_to_top (pre_label_order pre_pre_label_order (is_corrupt tr)) Public l

val meet_eq:
  tr:trace -> x:label -> y1:label -> y2:label ->
  Lemma
  (ensures meet y1 y2 `can_flow tr` x <==> (y1 `can_flow tr` x /\ y2 `can_flow tr` x))
  [SMTPat (meet y1 y2 `can_flow tr` x)] //Not sure about this
let meet_eq tr x y1 y2 =
  DY.Core.Label.Lattice.meet_eq (pre_label_order pre_pre_label_order (is_corrupt tr)) x y1 y2

val join_eq:
  tr:trace -> x1:label -> x2:label -> y:label ->
  Lemma
  (ensures y `can_flow tr` join x1 x2 <==> (y `can_flow tr` x1 /\ y `can_flow tr` x2))
  [SMTPat (y `can_flow tr` join x1 x2)] //Not sure about this
let join_eq tr x1 x2 y =
  DY.Core.Label.Lattice.join_eq (pre_label_order pre_pre_label_order (is_corrupt tr)) x1 x2 y

val principal_state_flow_to_public_eq:
  tr:trace -> prin:principal -> sess_id:nat ->
  Lemma
  (ensures (principal_state_label prin sess_id) `can_flow tr` public <==> was_corrupt tr prin sess_id)
  [SMTPat ((principal_state_label prin sess_id) `can_flow tr` public)] //Not sure about this
let principal_state_flow_to_public_eq tr prin sess_id =
  DY.Core.Label.Lattice.leaf_eq (pre_label_order pre_pre_label_order (is_corrupt tr)) Public (State (S prin sess_id))
