module DY.Core.Label.Derived

open DY.Core.Label.Type
open DY.Core.Trace.Base
open DY.Core.Label

/// This module defines auxillary predicates and lemmas
/// that are derived from the ones in DY.Core.Label.
/// In particular, they do not rely on the definition of `can_flow` or `is_corrupt`,
/// and only reason on them using lemmas exposed in DY.Core.Label.

val equivalent: trace -> label -> label -> prop
let equivalent tr l1 l2 =
  l1 `can_flow tr` l2 /\
  l2 `can_flow tr` l1

(*** Join flows to its operands ***)

val join_flows_to_left:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma ((l1 `join` l2) `can_flow tr` l1)
let join_flows_to_left tr l1 l2 =
  join_eq tr l1 l2 (join l1 l2)

val join_flows_to_right:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma ((l1 `join` l2) `can_flow tr` l2)
let join_flows_to_right tr l1 l2 =
  join_eq tr l1 l2 (join l1 l2)

(*** Join flows to its operand (with SMT patterns) ***)

val join_flows_to_left_smtpat:
  tr:trace ->
  l1:label -> l2:label -> l:label ->
  Lemma
  (requires l1 `can_flow tr` l)
  (ensures (l1 `join` l2) `can_flow tr` l)
  [SMTPat ((l1 `join` l2) `can_flow tr` l)]
let join_flows_to_left_smtpat tr l1 l2 l =
  join_flows_to_left tr l1 l2

val join_flows_to_right_smtpat:
  tr:trace ->
  l1:label -> l2:label -> l:label ->
  Lemma
  (requires l2 `can_flow tr` l)
  (ensures (l1 `join` l2) `can_flow tr` l)
  [SMTPat ((l1 `join` l2) `can_flow tr` l)]
let join_flows_to_right_smtpat tr l1 l2 l =
  join_flows_to_right tr l1 l2

(*** Operands flow to their meet ***)

val left_flows_to_meet:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma (l1 `can_flow tr` (l1 `meet` l2))
let left_flows_to_meet tr l1 l2 =
  meet_eq tr (meet l1 l2) l1 l2

val right_flows_to_meet:
  tr:trace ->
  l1:label -> l2:label ->
  Lemma (l2 `can_flow tr` (l1 `meet` l2))
let right_flows_to_meet tr l1 l2 =
  meet_eq tr (meet l1 l2) l1 l2

(*** Operands flow to their meet (with SMT patterns) ***)

val left_flows_to_meet_smtpat:
  tr:trace ->
  l:label -> l1:label -> l2:label ->
  Lemma
  (requires l `can_flow tr` l1)
  (ensures l `can_flow tr` (l1 `meet` l2))
  [SMTPat (l `can_flow tr` (l1 `meet` l2))]
let left_flows_to_meet_smtpat tr l l1 l2 =
  left_flows_to_meet tr l1 l2

val right_flows_to_meet_smtpat:
  tr:trace ->
  l:label -> l1:label -> l2:label ->
  Lemma
  (requires l `can_flow tr` l2)
  (ensures l `can_flow tr` (l1 `meet` l2))
  [SMTPat (l `can_flow tr` (l1 `meet` l2))]
let right_flows_to_meet_smtpat tr l l1 l2 =
  right_flows_to_meet tr l1 l2

(*** Equational theory for join ***)

val join_associative:
  l1:label -> l2:label -> l3:label ->
  Lemma
  (((l1 `join` l2) `join` l3) == (l1 `join` (l2 `join` l3)))
  [SMTPat ((l1 `join` l2) `join` l3); SMTPat (l1 `join` (l2 `join` l3))]
let join_associative l1 l2 l3 =
  intro_label_equal ((l1 `join` l2) `join` l3) (l1 `join` (l2 `join` l3)) (fun tr ->
    join_flows_to_left tr (l1 `join` l2) l3;
    join_eq tr l1 (l2 `join` l3) ((l1 `join` l2) `join` l3);
    join_flows_to_right tr l1 (l2 `join` l3);
    join_eq tr (l1 `join` l2) l3 (l1 `join` (l2 `join` l3))
  )

val join_commutes:
  l1:label -> l2:label ->
  Lemma
  ((l1 `join` l2) == (l2 `join` l1))
  [SMTPat (l1 `join` l2); SMTPat (l2 `join` l1)]
let join_commutes l1 l2 =
  intro_label_equal (l1 `join` l2) (l2 `join` l1) (fun tr -> ())

val join_label_public:
  l:label ->
  Lemma ((l `join` public) == public)
  [SMTPat (l `join` public)]
let join_label_public l =
  intro_label_equal (l `join` public) public (fun tr -> ())

val join_public_label:
  l:label ->
  Lemma ((public `join` l) == public)
  [SMTPat (public `join` l)]
let join_public_label l =
  intro_label_equal (public `join` l) public (fun tr -> ())

val join_label_secret:
  l:label ->
  Lemma ((l `join` secret) == l)
  [SMTPat (l `join` secret)]
let join_label_secret l =
  intro_label_equal (l `join` secret) l (fun tr -> ())

val join_secret_label:
  l:label ->
  Lemma ((secret `join` l) == l)
  [SMTPat (secret `join` l)]
let join_secret_label l =
  intro_label_equal (secret `join` l) l (fun tr -> ())

(*** Equational theory for meet ***)

val meet_associative:
  l1:label -> l2:label -> l3:label ->
  Lemma
  (((l1 `meet` l2) `meet` l3) == (l1 `meet` (l2 `meet` l3)))
  [SMTPat ((l1 `meet` l2) `meet` l3); SMTPat (l1 `meet` (l2 `meet` l3))]
let meet_associative l1 l2 l3 =
  intro_label_equal ((l1 `meet` l2) `meet` l3) (l1 `meet` (l2 `meet` l3)) (fun tr ->
    left_flows_to_meet tr (l1 `meet` l2) l3;
    meet_eq tr ((l1 `meet` l2) `meet` l3) l1 (l2 `meet` l3);
    right_flows_to_meet tr l1 (l2 `meet` l3);
    meet_eq tr (l1 `meet` (l2 `meet` l3)) (l1 `meet` l2) l3
  )

val meet_commutes:
  l1:label -> l2:label ->
  Lemma
  ((l1 `meet` l2) == (l2 `meet` l1))
  [SMTPat (l1 `meet` l2); SMTPat (l2 `meet` l1)]
let meet_commutes l1 l2 =
  intro_label_equal (l1 `meet` l2) (l2 `meet` l1) (fun tr -> ())

val meet_label_public:
  l:label ->
  Lemma ((l `meet` public) == l)
  [SMTPat (l `meet` public)]
let meet_label_public l =
  intro_label_equal (l `meet` public) l (fun tr -> ())

val meet_public_label:
  l:label ->
  Lemma ((public `meet` l) == l)
  [SMTPat (public `meet` l)]
let meet_public_label l =
  intro_label_equal (public `meet` l) l (fun tr -> ())

val meet_label_secret:
  l:label ->
  Lemma ((l `meet` secret) == secret)
  [SMTPat (l `meet` secret)]
let meet_label_secret l =
  intro_label_equal (l `meet` secret) secret (fun tr -> ())

val meet_secret_label:
  l:label ->
  Lemma ((secret `meet` l) == secret)
  [SMTPat (secret `meet` l)]
let meet_secret_label l =
  intro_label_equal (secret `meet` l) secret (fun tr -> ())
