module DY.Core.Label

open DY.Core.Label.Type
open DY.Core.Bytes.Type
open DY.Core.Trace.Type
open DY.Core.Trace.Base

#set-options "--fuel 0 --ifuel 0"

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

/// The monotonicity property of labels,
/// formulated the usual way.

val label_is_corrupt_later:
  l:label ->
  tr1:trace_ unit -> tr2:trace_ unit ->
  Lemma
  (requires
    l.is_corrupt tr1 /\
    tr1 <$ tr2
  )
  (ensures l.is_corrupt tr2)
let label_is_corrupt_later l tr1 tr2 =
  grows_induction_principle l.is_corrupt (fun tr ev ->
    l.is_corrupt_later;
    reveal_opaque (`%is_monotonic) is_monotonic
  ) tr1 tr2

/// Helper type and function to create labels.
/// This takes care of the restricted arrow type,
/// and the weird formulation of monotonicity in `is_corrupt_later`.

noeq
type label_constructor = {
  is_corrupt: trace_ unit -> prop;
  is_corrupt_later:
    tr1:trace_ unit -> tr2:trace_ unit ->
    Lemma
    (requires is_corrupt tr1 /\ tr1 <$ tr2)
    (ensures is_corrupt tr2)
  ;
}

#push-options "--fuel 1"
val mk_label: label_constructor -> label
let mk_label l = {
  is_corrupt = FStar.FunctionalExtensionality.on _ l.is_corrupt;
  is_corrupt_later = (
    reveal_opaque (`%is_monotonic) is_monotonic;
    reveal_opaque (`%grows) (grows #unit);
    norm_spec [zeta; delta_only [`%prefix]] (prefix #unit);
    assert(forall (tr:trace_ unit) ev. tr <$ (Snoc tr ev));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 l.is_corrupt_later)
  );
}
#pop-options

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
let is_corrupt tr l =
  l.is_corrupt (trace_forget_labels tr)

/// A key property of the corruption predicate is that it is monotone in the trace:
/// if a label `l` is corrupt now (in the trace `t1`), it will stay corrupt in the future (in the trace `t2`).

val is_corrupt_later:
  tr1:trace -> tr2:trace ->
  l:label ->
  Lemma
  (requires is_corrupt tr1 l /\ tr1 <$ tr2)
  (ensures is_corrupt tr2 l)
  [SMTPat (is_corrupt tr1 l); SMTPat (tr1 <$ tr2)]
let is_corrupt_later tr1 tr2 l =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  fmap_trace_later forget_label tr1 tr2;
  label_is_corrupt_later l (trace_forget_labels tr1) (trace_forget_labels tr2)

/// A label `l1` can flow to a label `l2` when `l2` will always be more secret than `l1` in the future,
/// or more precisely, when in the future, a corruption of `l2` implies a corruption of `l1`.

[@@"opaque_to_smt"]
val can_flow: trace -> label -> label -> prop
let can_flow tr l1 l2 =
  forall tr_extended. tr <$ tr_extended ==>
    (is_corrupt tr_extended l2 ==> is_corrupt tr_extended l1)

/// Extensionality theorems for labels

val intro_label_equal:
  l1:label -> l2:label ->
  (tr:trace -> Lemma (l1 `can_flow tr` l2 /\ l2 `can_flow tr` l1)) ->
  Lemma (l1 == l2)
let intro_label_equal l1 l2 pf =
  let open DY.Core.Label.Unknown in
  reveal_opaque (`%can_flow) can_flow;
  reveal_opaque (`%is_corrupt) is_corrupt;
  introduce forall tr. l1.is_corrupt tr == l2.is_corrupt tr with (
    pf (fmap_trace (replace_label unknown_label) tr);
    // These two lines prove surjectivity of `trace_forget_labels`
    // by showing that fmap_trace (forget_label public) is a right-inverse
    // (we could replace `unknown_label` with anything)
    fmap_trace_compose (replace_label unknown_label) forget_label forget_label tr;
    fmap_trace_identity forget_label tr;
    FStar.PropositionalExtensionality.apply (l1.is_corrupt tr) (l2.is_corrupt tr)
  );
  assert(l1.is_corrupt `FStar.FunctionalExtensionality.feq` l2.is_corrupt);
  assert(l1.is_corrupt == l2.is_corrupt);
  assert(l1.is_corrupt_later == l2.is_corrupt_later);
  ()


/// Functions to create labels.
/// They are useful so that the label type can remain abstract to the user.

[@@"opaque_to_smt"]
val secret: label
let secret = mk_label {
  is_corrupt = (fun tr -> False);
  is_corrupt_later = (fun tr1 tr2 -> ());
}

[@@"opaque_to_smt"]
val public: label
let public = mk_label {
  is_corrupt = (fun tr -> True);
  is_corrupt_later = (fun tr1 tr2 -> ());
}

[@@"opaque_to_smt"]
val meet: label -> label -> label
let meet l1 l2 = mk_label {
  is_corrupt = (fun tr -> l1.is_corrupt tr /\ l2.is_corrupt tr);
  is_corrupt_later = (fun tr1 tr2 ->
    label_is_corrupt_later l1 tr1 tr2;
    label_is_corrupt_later l2 tr1 tr2
  );
}

[@@"opaque_to_smt"]
val join: label -> label -> label
let join l1 l2 = mk_label {
  is_corrupt = (fun tr -> l1.is_corrupt tr \/ l2.is_corrupt tr);
  is_corrupt_later = (fun tr1 tr2 ->
    FStar.Classical.move_requires_3 label_is_corrupt_later l1 tr1 tr2;
    FStar.Classical.move_requires_3 label_is_corrupt_later l2 tr1 tr2
  );
}

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
  reveal_opaque (`%can_flow) can_flow;
  reveal_opaque (`%secret) secret;
  reveal_opaque (`%is_corrupt) is_corrupt

/// `secret` is the maximum of the label lattice.

val public_is_top:
  tr:trace -> l:label ->
  Lemma
  (ensures public `can_flow tr` l)
  [SMTPat (public `can_flow tr` l)]
let public_is_top tr l =
  reveal_opaque (`%can_flow) can_flow;
  reveal_opaque (`%public) public;
  reveal_opaque (`%is_corrupt) is_corrupt

/// `meet` satisfy the lower bound property.

val meet_eq:
  tr:trace -> x:label -> y1:label -> y2:label ->
  Lemma
  (ensures meet y1 y2 `can_flow tr` x <==> (y1 `can_flow tr` x /\ y2 `can_flow tr` x))
  [SMTPat (meet y1 y2 `can_flow tr` x)] //Not sure about this
let meet_eq tr x y1 y2 =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%meet) (meet)

/// `join` satisfy the upper bound property.

val join_eq:
  tr:trace -> x1:label -> x2:label -> y:label ->
  Lemma
  (ensures y `can_flow tr` join x1 x2 <==> (y `can_flow tr` x1 /\ y `can_flow tr` x2))
  [SMTPat (y `can_flow tr` join x1 x2)] //Not sure about this
let join_eq tr x1 x2 y =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join)

/// A label flows to `public` iff. it is corrupt.

val flow_to_public_eq:
  tr:trace -> l:label ->
  Lemma
  (ensures l `can_flow tr` public <==> is_corrupt tr l)
  [SMTPat (l `can_flow tr` public)] //Not sure about this
let flow_to_public_eq tr prin =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%public) (public)

/// A `join` flows to `public` iff. one of its operands flows to `public`.
/// This is a property specific to labels,
/// that is not implied by the standard lattice properties.

val join_flow_to_public_eq:
  tr:trace -> x1:label -> x2:label ->
  Lemma
  (ensures (join x1 x2) `can_flow tr` public <==> x1 `can_flow tr` public \/ x2 `can_flow tr` public)
  [SMTPat ((join x1 x2) `can_flow tr` public)] //Not sure about this
let join_flow_to_public_eq tr x1 x2 =
  reveal_opaque (`%is_corrupt) is_corrupt;
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%join) (join);
  reveal_opaque (`%public) (public)

/// Generic label for states:
/// `state_pred_label p` is corrupt when
/// there exists a corrupt `SetState` event satisfying the predicate `p`.
/// It can for example be used to depict any state of a principal
/// (e.g. as done by `principal_label`)

val state_pred_label_input: Type u#1
let state_pred_label_input =
  principal -> state_id -> bytes -> prop

[@@"opaque_to_smt"]
val state_pred_label:
  state_pred_label_input ->
  label
let state_pred_label p = mk_label {
  is_corrupt = (fun tr ->
    exists prin sess_id content.
      was_corrupt tr prin sess_id content /\
      p prin sess_id content
  );
  is_corrupt_later = (fun tr1 tr2 -> ());
}

val state_pred_label_input_can_flow:
  state_pred_label_input ->
  state_pred_label_input ->
  prop
let state_pred_label_input_can_flow p1 p2 =
  forall p s c. p2 p s c ==> p1 p s c

val state_pred_label_can_flow_state_pred_label:
  tr:trace ->
  p1:state_pred_label_input -> p2:state_pred_label_input ->
  Lemma
  (requires state_pred_label_input_can_flow p1 p2)
  (ensures state_pred_label p1 `can_flow tr` state_pred_label p2)
  [SMTPat (state_pred_label p1 `can_flow tr` state_pred_label p2)]
let state_pred_label_can_flow_state_pred_label tr p1 p2 =
  reveal_opaque (`%is_corrupt) is_corrupt;
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%state_pred_label) (state_pred_label)

val state_pred_label_can_flow_public:
  tr:trace ->
  p:state_pred_label_input ->
  Lemma (
    (state_pred_label p) `can_flow tr` public
    <==> (
      exists prin sess_id content.
        was_corrupt tr prin sess_id content /\
        p prin sess_id content
    )
  )
  [SMTPat ((state_pred_label p) `can_flow tr` public)]
let state_pred_label_can_flow_public tr p =
  reveal_opaque (`%is_corrupt) is_corrupt;
  reveal_opaque (`%state_pred_label) (state_pred_label);
  FStar.Classical.forall_intro (FStar.Classical.move_requires (event_exists_fmap_trace_eq forget_label tr));
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (event_at_fmap_trace_eq forget_label tr))

val principal_label_input:
  principal ->
  state_pred_label_input
let principal_label_input prin1 =
  fun prin2 _ _ ->
    prin1 == prin2

val principal_label: principal -> label
let principal_label prin =
  state_pred_label (principal_label_input prin)

val principal_state_label_input:
  principal -> state_id ->
  state_pred_label_input
let principal_state_label_input prin1 sess_id1 =
  fun prin2 sess_id2 _ ->
    prin1 == prin2 /\
    sess_id1 == sess_id2

val principal_state_label: principal -> state_id -> label
let principal_state_label prin sess_id =
  state_pred_label (principal_state_label_input prin sess_id)

val principal_state_content_label_input:
  principal -> state_id -> bytes ->
  state_pred_label_input
let principal_state_content_label_input prin1 sess_id1 content1 =
  fun prin2 sess_id2 content2 ->
    prin1 == prin2 /\
    sess_id1 == sess_id2 /\
    content1 == content2

val principal_state_content_label: principal -> state_id -> bytes -> label
let principal_state_content_label prin sess_id content =
  state_pred_label (principal_state_content_label_input prin sess_id content)
