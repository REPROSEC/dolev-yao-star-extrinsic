module DY.Core.Label

open DY.Core.Label.Type
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
  trace_forget_labels_later tr1 tr2;
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
    pf (fmap_trace (forget_label unknown_label) tr);
    // These two lines prove surjectivity of `trace_forget_labels`
    // by showing that fmap_trace (forget_label public) is a right-inverse
    // (we could replace `public` with anything)
    fmap_trace_compose (forget_label unknown_label) (forget_label ()) (forget_label ()) tr;
    fmap_trace_identity (forget_label ()) tr;
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

[@@"opaque_to_smt"]
val principal_label: principal -> label
let principal_label prin = mk_label {
  is_corrupt = (fun tr -> exists sess_id. was_corrupt tr prin sess_id);
  is_corrupt_later = (fun tr1 tr2 -> ());
}

[@@"opaque_to_smt"]
val principal_state_label: principal -> state_id -> label
let principal_state_label prin sess_id = mk_label {
  is_corrupt = (fun tr -> was_corrupt tr prin sess_id);
  is_corrupt_later = (fun tr1 tr2 -> ());
}

/// Injectivity properties of principal_label and principal_state_label.
/// We prove it by expliciting an inverse on the left (`extract_pre_label`).
/// This allows for an efficient SMT pattern,
/// compared to the standard injectivity definition,
/// whose SMT pattern would induce quadratic behavior.

type pre_label =
  | PreLabel_P: principal -> pre_label
  | PreLabel_S: principal -> state_id -> pre_label

val extract_pre_label_is_some:
  label -> principal & state_id ->
  prop
let extract_pre_label_is_some l (prin, sess_id) =
  l.is_corrupt (Snoc Nil (Corrupt prin sess_id))

[@@"opaque_to_smt"]
val extract_pre_label: label -> GTot (option pre_label)
let extract_pre_label l =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x. extract_pre_label_is_some l x) then (
    let (prin, sess_id) = FStar.IndefiniteDescription.indefinite_description_ghost _ (extract_pre_label_is_some l) in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (exists sess_id'. sess_id =!= sess_id' /\ l.is_corrupt (Snoc Nil (Corrupt prin sess_id'))) then (
      Some (PreLabel_P prin)
    ) else (
      Some (PreLabel_S prin sess_id)
    )
  ) else (
    None
  )

#push-options "--ifuel 1 --fuel 1"
val principal_label_injective:
  p:principal ->
  Lemma (extract_pre_label (principal_label p) == Some (PreLabel_P p))
  [SMTPat (principal_label p)]
let principal_label_injective p =
  normalize_term_spec extract_pre_label;
  normalize_term_spec principal_label;
  let l = principal_label p in
  let sess_id_0 = { the_id = 0} in
  let tr_0: trace_ unit = (Snoc Nil (Corrupt p sess_id_0)) in
  assert_norm(event_at tr_0 0 (Corrupt p sess_id_0));
  let sess_id_1 = { the_id = 1} in
  let tr_1: trace_ unit = (Snoc Nil (Corrupt p sess_id_1)) in
  assert_norm(event_at tr_1 0 (Corrupt p sess_id_1));
  assert(extract_pre_label_is_some l (p, sess_id_0))
#pop-options

#push-options "--ifuel 1 --fuel 1"
val principal_state_label_injective:
  p:principal -> s:state_id ->
  Lemma (extract_pre_label (principal_state_label p s) == Some (PreLabel_S p s))
  [SMTPat (principal_state_label p s)]
let principal_state_label_injective p s =
  normalize_term_spec extract_pre_label;
  normalize_term_spec principal_state_label;
  let l = principal_state_label p s in
  let tr: trace_ unit = (Snoc Nil (Corrupt p s)) in
  assert_norm(event_at tr 0 (Corrupt p s));
  assert(extract_pre_label_is_some l (p, s))
#pop-options

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

/// A principal flows to a particular state of this principal.

val principal_flow_to_principal_state:
  tr:trace -> prin:principal -> sess_id:state_id ->
  Lemma
  (ensures (principal_label prin) `can_flow tr` (principal_state_label prin sess_id))
  [SMTPat ((principal_label prin) `can_flow tr` (principal_state_label prin sess_id))]
let principal_flow_to_principal_state tr prin sess_id =
  reveal_opaque (`%is_corrupt) is_corrupt;
  reveal_opaque (`%can_flow) can_flow;
  reveal_opaque (`%principal_label) principal_label;
  reveal_opaque (`%principal_state_label) principal_state_label

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
