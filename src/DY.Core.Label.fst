module DY.Core.Label

open DY.Core.Bytes.Type
open DY.Core.Label.Type
open DY.Core.Trace.Type

class label_description_flow = {
  get_description: content:bytes -> bytes;
  desc_can_flow: bytes -> bytes -> prop;
  desc_can_flow_refl: x:bytes -> Lemma (x `desc_can_flow` x);
  desc_can_flow_trans: x:bytes -> y:bytes -> z:bytes ->
    Lemma
    (requires x `desc_can_flow` y /\ y `desc_can_flow` z)
    (ensures x `desc_can_flow` z);
}

val description_order:
  {|label_description_flow|} ->
  DY.Core.Label.Lattice.order bytes
let description_order #ldf = {
  rel = (fun x y -> desc_can_flow y x);
  refl = (fun x -> desc_can_flow_refl x);
  trans = (fun x y z ->
    desc_can_flow_trans z y x
  );
}

val pre_can_flow:
  {|label_description_flow|} ->
  pre_pre_label bytes -> pre_pre_label bytes -> prop
let pre_can_flow #ldf who1 who2 =
  who2 `(pre_pre_label_order description_order).rel` who1

val pre_can_flow_refl:
  {|label_description_flow|} ->
  who:pre_pre_label bytes ->
  Lemma
  (ensures who `pre_can_flow` who)
  [SMTPat (who `pre_can_flow` who)]
let pre_can_flow_refl #ldf who =
  (pre_pre_label_order description_order).refl who

val pre_can_flow_transitive:
  {|label_description_flow|} ->
  who1:pre_pre_label bytes -> who2:pre_pre_label bytes -> who3:pre_pre_label bytes ->
  Lemma
  (requires who1 `pre_can_flow` who2 /\ who2 `pre_can_flow` who3)
  (ensures who1 `pre_can_flow` who3)
  [SMTPat (who1 `pre_can_flow` who2); SMTPat (who1 `pre_can_flow` who3)]
let pre_can_flow_transitive #ldf who1 who2 who3 =
  (pre_pre_label_order description_order).trans who3 who2 who1

val is_corrupt: {|label_description_flow|} -> trace -> pre_pre_label bytes -> prop
let is_corrupt #ldf tr who =
  exists prin content.
    who `pre_can_flow` (S prin (get_description content)) /\
    state_was_corrupt tr prin content

val is_corrupt_later:
  {|label_description_flow|} ->
  tr1:trace -> tr2:trace ->
  who:pre_pre_label bytes ->
  Lemma
  (requires is_corrupt tr1 who /\ tr1 <$ tr2)
  (ensures is_corrupt tr2 who)
  [SMTPat (is_corrupt tr1 who); SMTPat (tr1 <$ tr2)]
let is_corrupt_later #ldf tr1 tr2 who = ()

val is_corrupt_order:
  {|label_description_flow|} ->
  tr:trace ->
  who1:pre_pre_label bytes -> who2:pre_pre_label bytes ->
  Lemma
  (requires is_corrupt tr who1 /\ who2 `pre_can_flow` who1)
  (ensures is_corrupt tr who2)
  // TODO SMT pattern is weird, refactor
  [SMTPat (is_corrupt tr who1); SMTPat (who1 `(pre_pre_label_order description_order).rel` who2)]
let is_corrupt_order #ldf tr who1 who2 = ()

type label = label bytes

[@@"opaque_to_smt"]
val can_flow: {|label_description_flow|} -> trace -> label -> label -> prop
let can_flow #ldf tr l1 l2 =
  l2 `(label_order description_order (is_corrupt tr)).rel` l1

[@@"opaque_to_smt"]
val secret: label
let secret =
  DY.Core.Label.Lattice.Leaf Secret

[@@"opaque_to_smt"]
val public: label
let public =
  DY.Core.Label.Lattice.Leaf Public

[@@"opaque_to_smt"]
val meet: label -> label -> label
let meet l1 l2 =
  DY.Core.Label.Lattice.Meet l1 l2

[@@"opaque_to_smt"]
val join: label -> label -> label
let join l1 l2 =
  DY.Core.Label.Lattice.Join l1 l2

[@@"opaque_to_smt"]
val principal_label: principal -> label
let principal_label prin =
  DY.Core.Label.Lattice.Leaf (State (P prin))

[@@"opaque_to_smt"]
val principal_state_label: principal -> bytes -> label
let principal_state_label prin sess_id =
  DY.Core.Label.Lattice.Leaf (State (S prin sess_id))

[@@"opaque_to_smt"]
val principal_corrupt: {|label_description_flow|} -> trace -> principal -> prop
let principal_corrupt #ldf tr prin =
  is_corrupt tr (P prin)

[@@"opaque_to_smt"]
val principal_state_corrupt: {|label_description_flow|} -> trace -> principal -> bytes -> prop
let principal_state_corrupt #ldf tr prin sess_id =
  is_corrupt tr (S prin sess_id)

val principal_label_injective:
  p1:principal -> p2:principal ->
  Lemma
  (requires principal_label p1 == principal_label p2)
  (ensures p1 == p2)
  [SMTPat (principal_label p1); SMTPat (principal_label p2)]
let principal_label_injective p1 p2 =
  normalize_term_spec principal_label

val principal_state_label_injective:
  p1:principal -> s1:bytes -> p2:principal -> s2:bytes ->
  Lemma
  (requires principal_state_label p1 s1 == principal_state_label p2 s2)
  (ensures p1 == p2 /\ s1 == s2)
  [SMTPat (principal_state_label p1 s1); SMTPat (principal_state_label p2 s2)]
let principal_state_label_injective p1 s1 p2 s2 =
  normalize_term_spec principal_state_label

val principal_corrupt_later:
  {|label_description_flow|} ->
  tr1:trace -> tr2:trace ->
  prin:principal ->
  Lemma
  (requires principal_corrupt tr1 prin /\ tr1 <$ tr2)
  (ensures principal_corrupt tr2 prin)
  [SMTPat (principal_corrupt tr1 prin); SMTPat (tr1 <$ tr2)]
let principal_corrupt_later #ldf tr1 tr2 prin =
  assert_norm(principal_corrupt tr1 prin == is_corrupt tr1 (P prin));
  assert_norm(principal_corrupt tr2 prin == is_corrupt tr2 (P prin))

val principal_state_corrupt_later:
  {|label_description_flow|} ->
  tr1:trace -> tr2:trace ->
  prin:principal -> sess_id:bytes ->
  Lemma
  (requires principal_state_corrupt tr1 prin sess_id /\ tr1 <$ tr2)
  (ensures principal_state_corrupt tr2 prin sess_id)
  [SMTPat (principal_state_corrupt tr1 prin sess_id); SMTPat (tr1 <$ tr2)]
let principal_state_corrupt_later #ldf tr1 tr2 prin sess_id =
  assert_norm(principal_state_corrupt tr1 prin sess_id == is_corrupt tr1 (S prin sess_id));
  assert_norm(principal_state_corrupt tr2 prin sess_id == is_corrupt tr2 (S prin sess_id))

val state_was_corrupt_implies_principal_state_corrupt:
  {|label_description_flow|} ->
  tr:trace ->
  prin:principal -> content:bytes ->
  Lemma
  (requires state_was_corrupt tr prin content)
  (ensures principal_state_corrupt tr prin (get_description content))
  [SMTPat (state_was_corrupt tr prin content); SMTPat (principal_state_corrupt tr prin (get_description content))]
let state_was_corrupt_implies_principal_state_corrupt #ldf tr prin content =
  assert_norm(principal_state_corrupt tr prin (get_description content) == is_corrupt tr (S prin (get_description content)))

val can_flow_reflexive:
  {|label_description_flow|} ->
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` l)
  [SMTPat (l `can_flow tr` l)]
let can_flow_reflexive #ldf tr l =
  normalize_term_spec can_flow;
  (label_order description_order (is_corrupt tr)).refl l

val can_flow_transitive:
  {|label_description_flow|} ->
  tr:trace -> l1:label -> l2:label -> l3:label ->
  Lemma
  (requires l1 `can_flow tr` l2 /\ l2 `can_flow tr` l3)
  (ensures l1 `can_flow tr` l3)
  [SMTPat (l1 `can_flow tr` l3); SMTPat (l1 `can_flow tr` l2)]
let can_flow_transitive #ldf tr l1 l2 l3 =
  normalize_term_spec can_flow;
  (label_order description_order (is_corrupt tr)).trans l3 l2 l1

val can_flow_later:
  {|label_description_flow|} ->
  tr1:trace -> tr2:trace ->
  l1:label -> l2:label ->
  Lemma
  (requires l1 `can_flow tr1` l2 /\ tr1 <$ tr2)
  (ensures l1 `can_flow tr2` l2)
  [SMTPat (l1 `can_flow tr1` l2); SMTPat (tr1 <$ tr2)]
let can_flow_later #ldf tr1 tr2 l1 l2 =
  normalize_term_spec can_flow;
  DY.Core.Label.Lattice.lattice_order_monotone (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr1)) (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr2)) l2 l1

val secret_is_bottom:
  {|label_description_flow|} ->
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` secret)
  [SMTPat (l `can_flow tr` secret)]
let secret_is_bottom #ldf tr l =
  normalize_term_spec can_flow;
  normalize_term_spec secret;
  DY.Core.Label.Lattice.bottom_to_bottom (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr)) Secret l

val public_is_top:
  {|label_description_flow|} ->
  tr:trace -> l:label ->
  Lemma
  (ensures public `can_flow tr` l)
  [SMTPat (public `can_flow tr` l)]
let public_is_top #ldf tr l =
  normalize_term_spec can_flow;
  normalize_term_spec public;
  DY.Core.Label.Lattice.top_to_top (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr)) Public l

val meet_eq:
  {|label_description_flow|} ->
  tr:trace -> x:label -> y1:label -> y2:label ->
  Lemma
  (ensures meet y1 y2 `can_flow tr` x <==> (y1 `can_flow tr` x /\ y2 `can_flow tr` x))
  [SMTPat (meet y1 y2 `can_flow tr` x)] //Not sure about this
let meet_eq #ldf tr x y1 y2 =
  normalize_term_spec can_flow;
  normalize_term_spec meet;
  DY.Core.Label.Lattice.meet_eq (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr)) x y1 y2

val join_eq:
  {|label_description_flow|} ->
  tr:trace -> x1:label -> x2:label -> y:label ->
  Lemma
  (ensures y `can_flow tr` join x1 x2 <==> (y `can_flow tr` x1 /\ y `can_flow tr` x2))
  [SMTPat (y `can_flow tr` join x1 x2)] //Not sure about this
let join_eq #ldf tr x1 x2 y =
  normalize_term_spec can_flow;
  normalize_term_spec join;
  DY.Core.Label.Lattice.join_eq (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr)) x1 x2 y

val principal_flow_to_public_eq:
  {|label_description_flow|} ->
  tr:trace -> prin:principal ->
  Lemma
  (ensures (principal_label prin) `can_flow tr` public <==> principal_corrupt tr prin)
  [SMTPat ((principal_label prin) `can_flow tr` public)] //Not sure about this
let principal_flow_to_public_eq #ldf tr prin =
  normalize_term_spec can_flow;
  normalize_term_spec principal_label;
  normalize_term_spec public;
  assert_norm(principal_corrupt tr prin == is_corrupt tr (P prin));
  DY.Core.Label.Lattice.leaf_eq (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr)) Public (State (P prin))

val principal_state_flow_to_public_eq:
  {|label_description_flow|} ->
  tr:trace -> prin:principal -> sess_id:bytes ->
  Lemma
  (ensures (principal_state_label prin sess_id) `can_flow tr` public <==> principal_state_corrupt tr prin sess_id)
  [SMTPat ((principal_state_label prin sess_id) `can_flow tr` public)] //Not sure about this
let principal_state_flow_to_public_eq #ldf tr prin sess_id =
  normalize_term_spec can_flow;
  normalize_term_spec principal_state_label;
  normalize_term_spec public;
  assert_norm(principal_state_corrupt tr prin sess_id == is_corrupt tr (S prin sess_id));
  DY.Core.Label.Lattice.leaf_eq (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr)) Public (State (S prin sess_id))

val principal_flow_to_principal_state:
  {|label_description_flow|} ->
  tr:trace -> prin:principal -> sess_id:bytes ->
  Lemma
  (ensures (principal_label prin) `can_flow tr` (principal_state_label prin sess_id))
  [SMTPat ((principal_label prin) `can_flow tr` (principal_state_label prin sess_id))]
let principal_flow_to_principal_state #ldf tr prin sess_id =
  normalize_term_spec can_flow;
  normalize_term_spec principal_label;
  normalize_term_spec principal_state_label

val join_flow_to_public_eq:
  {|label_description_flow|} ->
  tr:trace -> x1:label -> x2:label ->
  Lemma
  (ensures (join x1 x2) `can_flow tr` public <==> x1 `can_flow tr` public \/ x2 `can_flow tr` public)
  [SMTPat ((join x1 x2) `can_flow tr` public)] //Not sure about this
let join_flow_to_public_eq #ldf tr x1 x2 =
  normalize_term_spec can_flow;
  normalize_term_spec join;
  normalize_term_spec public;
  DY.Core.Label.Lattice.leaf_less_join (pre_label_order (pre_pre_label_order description_order) (is_corrupt tr)) Public x1 x2
