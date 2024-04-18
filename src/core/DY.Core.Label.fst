module DY.Core.Label

open DY.Core.Label.Type
open DY.Core.Trace.Type

/// This module define the notion of corruption of a label (`is_corrupt`),
/// and the flow relation between labels (`can_flow`),
/// along with theorems that can be used to reason on the label flow.
///
/// Labels are an over-approximation on the set of principals to corrupt
/// for an attacker to know some particular bytestring.
/// More precisely, if an attacker knows some bytestring b,
/// then it must have corrupt some set of principals depicted by the label of b.
/// (This fact is formally proved in DY.Core.Attacker.Knowledge.attacker_only_knows_publishable_values.)
///
/// Given this description, one might think that the label of b is simply a set,
/// namely the smallest set of principals to corrupt in order to compute the bytestring b.
/// In reality, labels are more complex than sets of principals.
/// Indeed, consider a bytestring b
/// which is shared secret between Alice and Bob
/// mixed (e.g. using a KDF) with a shared secret between Bob and Charlie.
/// This secret could be computed by the attacker by doing corruptions,
/// either by corrupting Bob,
/// or by corrupting both Alice and Charlie.
/// Labels over-approximate the actual knowledge of the attacker:
/// in the example above, Alice might not store the key to compute its shared secret with Bob,
/// hence even by corrupting Alice and Charlie,
/// the attacker would not be able to compute b.
///
/// Some secrets bytestrings are less secret than other.
/// For example, if Alice and Bob share a secret using a Diffie-Hellman computation,
/// then the shared secret is less secret than Alice's Diffie-Hellman private key,
/// because the latter can be used to compute the former.
/// This notion of "less secret" is lifted to labels,
/// using the flow relation (`can_flow`).


val get_principal: pre_label -> option principal
let get_principal l =
  match l with
  | P p -> Some p
  | S p _ -> Some p

val get_session: pre_label -> option nat
let get_session l =
  match l with
  | P _ -> None
  | S _ s -> Some s

/// When is a pre-label less secret than another?
/// This encodes the fact that `P p` is less secret than `S p s`.

val pre_can_flow:
  pre_label -> pre_label ->
  prop
let pre_can_flow x y =
  match x with
  | P p -> Some p == get_principal y
  | S p s -> Some p == get_principal y /\ Some s == get_session y

/// A pre-label is corrupt when there exists a corresponding corruption event in the trace.

[@@"opaque_to_smt"]
val pre_is_corrupt: trace -> pre_label -> prop
let pre_is_corrupt tr who =
  exists prin sess_id.
    who `pre_can_flow` (S prin sess_id) /\
    was_corrupt tr prin sess_id

/// If the attacker knows a value with label `l`, then it must have done some corruptions in the trace.
/// The corruption predicate express whether values with label `l` are still secure,
/// with respect to corruption events in the trace.
/// For example:
/// - a public value can always be known to the attacker, so the label `public` is always corrupt.
/// - a shared secret between Alice and Bob has the label `join (principal "Alice") (principal "Bob")`,
///   and to obtain this secret, the attacker has to corrupt either Alice or Bob.
/// Given this intuition on the corruption predicate, its definition follows.

[@@"opaque_to_smt"]
val is_corrupt: trace -> label -> prop
let rec is_corrupt tr l =
  match l with
  | Secret -> False
  | State s -> pre_is_corrupt tr s
  | Meet l1 l2 -> is_corrupt tr l1 /\ is_corrupt tr l2
  | Join l1 l2 -> is_corrupt tr l1 \/ is_corrupt tr l2
  | Public -> True

/// A key property of the corruption predicate is that it is monotone in the trace:
/// if a label `l` is corrupt now (in the trace `t1`), it will stay corrupt in the future (in the trace `t2`).

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

/// A label `l1` can flow to a label `l2` when `l2` will always be more secret than `l1` in the future,
/// or more precisely, when in the future, a corruption of `l2` implies a corruption of `l1`.

[@@"opaque_to_smt"]
val can_flow: trace -> label -> label -> prop
let can_flow tr l1 l2 =
  forall tr_extended. tr <$ tr_extended ==>
    (is_corrupt tr_extended l2 ==> is_corrupt tr_extended l1)

/// Functions to create labels.
/// They are useful so that the label type can remain abstract to the user.

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

/// Injectivity properties of principal_label and principal_state_label.
/// We prove it by expliciting an inverse on the left (`extract_pre_label`).
/// This allows for an efficient SMT pattern,
/// compared to the standard injectivity definition,
/// whose SMT pattern would induce quadratic behavior.

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

/// `can_flow tr` is reflexive.

val can_flow_reflexive:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` l)
  [SMTPat (l `can_flow tr` l)]
let can_flow_reflexive tr l =
  normalize_term_spec can_flow

/// `can_flow tr` is transitive.

val can_flow_transitive:
  tr:trace -> l1:label -> l2:label -> l3:label ->
  Lemma
  (requires l1 `can_flow tr` l2 /\ l2 `can_flow tr` l3)
  (ensures l1 `can_flow tr` l3)
  [SMTPat (l1 `can_flow tr` l3); SMTPat (l1 `can_flow tr` l2)]
let can_flow_transitive tr l1 l2 l3 =
  normalize_term_spec can_flow

/// `can_flow tr` is monotone in the trace.

val can_flow_later:
  tr1:trace -> tr2:trace ->
  l1:label -> l2:label ->
  Lemma
  (requires l1 `can_flow tr1` l2 /\ tr1 <$ tr2)
  (ensures l1 `can_flow tr2` l2)
  [SMTPat (l1 `can_flow tr1` l2); SMTPat (tr1 <$ tr2)]
let can_flow_later tr1 tr2 l1 l2 =
  reveal_opaque (`%can_flow) (can_flow)

/// `secret` is the minimum of the label lattice.

val secret_is_bottom:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` secret)
  [SMTPat (l `can_flow tr` secret)]
let secret_is_bottom tr l =
  normalize_term_spec can_flow;
  normalize_term_spec secret

/// `secret` is the maximum of the label lattice.

val public_is_top:
  tr:trace -> l:label ->
  Lemma
  (ensures public `can_flow tr` l)
  [SMTPat (public `can_flow tr` l)]
let public_is_top tr l =
  normalize_term_spec can_flow;
  normalize_term_spec public

/// `meet` satisfy the lower bound property.

val meet_eq:
  tr:trace -> x:label -> y1:label -> y2:label ->
  Lemma
  (ensures meet y1 y2 `can_flow tr` x <==> (y1 `can_flow tr` x /\ y2 `can_flow tr` x))
  [SMTPat (meet y1 y2 `can_flow tr` x)] //Not sure about this
let meet_eq tr x y1 y2 =
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%meet) (meet)

/// `join` satisfy the upper bound property.

val join_eq:
  tr:trace -> x1:label -> x2:label -> y:label ->
  Lemma
  (ensures y `can_flow tr` join x1 x2 <==> (y `can_flow tr` x1 /\ y `can_flow tr` x2))
  [SMTPat (y `can_flow tr` join x1 x2)] //Not sure about this
let join_eq tr x1 x2 y =
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join)

/// A label flows to `public` iff. it is corrupt.

val flow_to_public_eq:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` public <==> is_corrupt tr l)
  [SMTPat (l `can_flow tr` public)] //Not sure about this
let flow_to_public_eq tr prin =
  norm_spec [zeta; delta_only [`%is_corrupt]] (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%public) (public)

/// A principal flows to a particular state of this principal.

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

/// A `join` flows to `public` iff. one of its operands flows to `public`.
/// This is a property specific to labels,
/// that is not implied by the standard lattice properties.

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
