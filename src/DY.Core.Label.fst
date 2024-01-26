module DY.Core.Label

open DY.Core.Label.Type
open DY.Core.Trace.Type

[@@"opaque_to_smt"]
val pre_is_corrupt: trace -> pre_label -> prop
let pre_is_corrupt tr who =
  exists prin sess_id.
    (S prin sess_id) `pre_label_order.rel` who /\
    was_corrupt tr prin sess_id

[@@"opaque_to_smt"]
val is_corrupt: trace -> label -> prop
let rec is_corrupt tr l =
  match l with
  | Secret -> False
  | State s -> pre_is_corrupt tr s
  | Meet l1 l2 -> is_corrupt tr l1 /\ is_corrupt tr l2
  | Join l1 l2 -> is_corrupt tr l1 \/ is_corrupt tr l2
  | Public -> True

val is_corrupt_later:
  tr1:trace -> tr2:trace ->
  l:label ->
  Lemma
  (requires is_corrupt tr1 l /\ tr1 <$ tr2)
  (ensures is_corrupt tr2 l)
  [SMTPat (is_corrupt tr1 l); SMTPat (tr1 <$ tr2)]
let rec is_corrupt_later tr1 tr2 l =
  reveal_opaque (`%pre_is_corrupt) (pre_is_corrupt);
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  match l with
  | Secret
  | Public
  | State _ -> ()
  | Meet l1 l2
  | Join l1 l2 ->
    introduce is_corrupt tr1 l1 ==> is_corrupt tr2 l1 with _. is_corrupt_later tr1 tr2 l1;
    introduce is_corrupt tr1 l2 ==> is_corrupt tr2 l2 with _. is_corrupt_later tr1 tr2 l2

[@@"opaque_to_smt"]
val can_flow: trace -> label -> label -> prop
let can_flow tr l1 l2 =
  forall tr_extended. tr <$ tr_extended ==>
    (is_corrupt tr_extended l2 ==> is_corrupt tr_extended l1)

[@@"opaque_to_smt"]
val secret: label
let secret =
  Secret

[@@"opaque_to_smt"]
val public: label
let public =
  Public

[@@"opaque_to_smt"]
val meet: label -> label -> label
let meet l1 l2 =
  Meet l1 l2

[@@"opaque_to_smt"]
val join: label -> label -> label
let join l1 l2 =
  Join l1 l2

[@@"opaque_to_smt"]
val principal_label: principal -> label
let principal_label prin =
  State (P prin)

[@@"opaque_to_smt"]
val principal_state_label: principal -> nat -> label
let principal_state_label prin sess_id =
  State (S prin sess_id)

[@@"opaque_to_smt"]
val extract_pre_label: label -> GTot (option pre_label)
let extract_pre_label l =
  match l with
  | State s -> Some s
  | _ -> None

val principal_label_injective:
  p:principal ->
  Lemma (extract_pre_label (principal_label p) == Some (P p))
  [SMTPat (principal_label p)]
let principal_label_injective p =
  normalize_term_spec extract_pre_label;
  normalize_term_spec principal_label

val principal_state_label_injective:
  p:principal -> s:nat ->
  Lemma (extract_pre_label (principal_state_label p s) == Some (S p s))
  [SMTPat (principal_state_label p s)]
let principal_state_label_injective p s =
  normalize_term_spec extract_pre_label;
  normalize_term_spec principal_state_label

val can_flow_reflexive:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` l)
  [SMTPat (l `can_flow tr` l)]
let can_flow_reflexive tr l =
  normalize_term_spec can_flow

val can_flow_transitive:
  tr:trace -> l1:label -> l2:label -> l3:label ->
  Lemma
  (requires l1 `can_flow tr` l2 /\ l2 `can_flow tr` l3)
  (ensures l1 `can_flow tr` l3)
  [SMTPat (l1 `can_flow tr` l3); SMTPat (l1 `can_flow tr` l2)]
let can_flow_transitive tr l1 l2 l3 =
  normalize_term_spec can_flow

val can_flow_later:
  tr1:trace -> tr2:trace ->
  l1:label -> l2:label ->
  Lemma
  (requires l1 `can_flow tr1` l2 /\ tr1 <$ tr2)
  (ensures l1 `can_flow tr2` l2)
  [SMTPat (l1 `can_flow tr1` l2); SMTPat (tr1 <$ tr2)]
let can_flow_later tr1 tr2 l1 l2 =
  reveal_opaque (`%can_flow) (can_flow)

val secret_is_bottom:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` secret)
  [SMTPat (l `can_flow tr` secret)]
let secret_is_bottom tr l =
  normalize_term_spec can_flow;
  normalize_term_spec secret

val public_is_top:
  tr:trace -> l:label ->
  Lemma
  (ensures public `can_flow tr` l)
  [SMTPat (public `can_flow tr` l)]
let public_is_top tr l =
  normalize_term_spec can_flow;
  normalize_term_spec public

val meet_eq:
  tr:trace -> x:label -> y1:label -> y2:label ->
  Lemma
  (ensures meet y1 y2 `can_flow tr` x <==> (y1 `can_flow tr` x /\ y2 `can_flow tr` x))
  [SMTPat (meet y1 y2 `can_flow tr` x)] //Not sure about this
let meet_eq tr x y1 y2 =
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%meet) (meet)

val join_eq:
  tr:trace -> x1:label -> x2:label -> y:label ->
  Lemma
  (ensures y `can_flow tr` join x1 x2 <==> (y `can_flow tr` x1 /\ y `can_flow tr` x2))
  [SMTPat (y `can_flow tr` join x1 x2)] //Not sure about this
let join_eq tr x1 x2 y =
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join)

val flow_to_public_eq:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` public <==> is_corrupt tr l)
  [SMTPat (l `can_flow tr` public)] //Not sure about this
let flow_to_public_eq tr prin =
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%public) (public)

val principal_flow_to_principal_state:
  tr:trace -> prin:principal -> sess_id:nat ->
  Lemma
  (ensures (principal_label prin) `can_flow tr` (principal_state_label prin sess_id))
  [SMTPat ((principal_label prin) `can_flow tr` (principal_state_label prin sess_id))]
let principal_flow_to_principal_state tr prin sess_id =
  reveal_opaque (`%pre_is_corrupt) (pre_is_corrupt);
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  normalize_term_spec can_flow;
  normalize_term_spec principal_label;
  normalize_term_spec principal_state_label

val join_flow_to_public_eq:
  tr:trace -> x1:label -> x2:label ->
  Lemma
  (ensures (join x1 x2) `can_flow tr` public <==> x1 `can_flow tr` public \/ x2 `can_flow tr` public)
  [SMTPat ((join x1 x2) `can_flow tr` public)] //Not sure about this
let join_flow_to_public_eq tr x1 x2 =
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join);
  reveal_opaque (`%public) (public)
