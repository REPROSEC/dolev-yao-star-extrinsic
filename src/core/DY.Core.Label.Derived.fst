module DY.Core.Label.Derived

open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Label

/// This module defines auxillary predicates and lemmas
/// that are derived from the ones in DY.Core.Label.
/// In particular, they do not rely on the definition of `can_flow` or `is_corrupt`,
/// and only reason on them using lemmas exposed in DY.Core.Label.

val equivalent: trace -> label -> label -> prop
let equivalent tr l1 l2 =
  l1 `can_flow tr` l2 /\
  l2 `can_flow tr` l1

val always_equivalent: label -> label -> prop
let always_equivalent l1 l2 =
  forall tr. l1 `equivalent tr` l2

val introduce_always_equivalent:
  l1:label -> l2:label ->
  (tr:trace -> Lemma(l1 `equivalent tr` l2)) ->
  Lemma (l1 `always_equivalent` l2)
let introduce_always_equivalent l1 l2 pf =
  introduce forall tr. l1 `equivalent tr` l2 with pf tr

val join_commutes:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma
  ((l1 `join` l2) `equivalent tr` (l2 `join` l1))
let join_commutes tr l1 l2 =
  join_eq tr l1 l2 (join l1 l2);
  join_eq tr l2 l1 (join l2 l1)

val join_always_commutes:
  l1:label -> l2:label ->
  Lemma
  ((l1 `join` l2) `always_equivalent` (l2 `join` l1))
let join_always_commutes l1 l2 =
  introduce_always_equivalent (l1 `join` l2) (l2 `join` l1) (fun tr -> join_commutes tr l1 l2)

val meet_commutes:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma
  ((l1 `meet` l2) `equivalent tr` (l2 `meet` l1))
let meet_commutes tr l1 l2 =
  meet_eq tr (meet l1 l2) l1 l2;
  meet_eq tr (meet l2 l1) l2 l1

val meet_always_commutes:
  l1:label -> l2:label ->
  Lemma
  ((l1 `meet` l2) `always_equivalent` (l2 `meet` l1))
let meet_always_commutes l1 l2 =
  introduce_always_equivalent (l1 `meet` l2) (l2 `meet` l1) (fun tr -> meet_commutes tr l1 l2)

val join_flows_to_left:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma ((l1 `join` l2) `can_flow tr` l1)
  [SMTPat ((l1 `join` l2) `can_flow tr` l1)]
let join_flows_to_left tr l1 l2 =
  join_eq tr l1 l2 (join l1 l2)

val join_flows_to_right:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma ((l1 `join` l2) `can_flow tr` l2)
  [SMTPat ((l1 `join` l2) `can_flow tr` l2)]
let join_flows_to_right tr l1 l2 =
  join_eq tr l1 l2 (join l1 l2)

val left_flows_to_meet:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma (l1 `can_flow tr` (l1 `meet` l2))
  [SMTPat (l1 `can_flow tr` (l1 `meet` l2))]
let left_flows_to_meet tr l1 l2 =
  meet_eq tr (meet l1 l2) l1 l2

val right_flows_to_meet:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma (l2 `can_flow tr` (l1 `meet` l2))
  [SMTPat (l2 `can_flow tr` (l1 `meet` l2))]
let right_flows_to_meet tr l1 l2 =
  meet_eq tr (meet l1 l2) l1 l2
