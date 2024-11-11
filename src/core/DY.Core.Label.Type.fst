module DY.Core.Label.Type

open FStar.FunctionalExtensionality
open DY.Core.Trace.Type

/// This module defines the types associated with labels.
/// It is separated from functions and predicates on labels
/// in order to avoid dependency cycles.
///
/// In full generality, a label is a predicate on the trace
/// stating whether the attacker has performed some amount of corruption
/// (see DY.Core.Label for more explanations).
///
/// We therefore want labels to be predicates `trace -> prop`,
/// however this doesn't work with F*'s positivity checker.
/// (see https://fstar-lang.org/tutorial/book/part2/part2_inductive_type_families.html#strictly-positive-definitions )
/// Indeed, we want the trace to contain labels (see `RandGen` entry),
/// and we want labels to be predicates on the trace, namely `trace -> prop` (see DY.Core.Label.Type).
/// A type `t` cannot contain `t -> prop` because this could be used to derive False (using Cantor's diagonal argument).
/// To circumvent that, labels are predicates on traces with no labels (i.e. whose label type is `unit`).
/// This solves the positivity issue because `trace_ label` contain labels that are `trace_ unit -> prop`,
/// which respects the positivity condition.
/// It means that labels cannot decide about their corruption depending on other labels in the trace,
/// but this is not a problem in practice.
///
/// We use the restricted arrow type `^->` to benefit from predicate extensionality.
/// This implies that two labels that behave the same are equal, see `DY.Core.Label.intro_label_equal`.

#set-options "--fuel 0 --ifuel 0"

/// Monotonicity property of labels.
/// This is hidden from the SMT to avoid polluting the context with the content of `is_corrupt_later` for each label.
/// `is_corrupt_later` is a `squash` rather than a `Lemma` to better prove extensionality.
/// Monotonicity is not formulated with the `<$` relation as in the rest of DY*
/// to simplify the dependency graph.

[@@"opaque_to_smt"]
val is_monotonic:
  (trace_ unit -> prop) ->
  prop
let is_monotonic is_corrupt =
  forall tr entry. is_corrupt tr ==> is_corrupt (Snoc tr entry)

[@@erasable]
noeq
type label = {
  is_corrupt: trace_ unit ^-> prop;
  is_corrupt_later: squash (is_monotonic is_corrupt);
}
