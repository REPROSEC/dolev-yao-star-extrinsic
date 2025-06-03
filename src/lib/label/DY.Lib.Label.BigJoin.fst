module DY.Lib.Label.BigJoin

open DY.Core

#set-options "--fuel 0 --ifuel 0"

/// `big_join` is like `join`, over a possibly unbounded domain.

[@@"opaque_to_smt"]
val big_join:
  #a:Type ->
  (a -> label) ->
  label
let big_join #a f = mk_label {
  is_corrupt = (fun tr ->
    exists x. (f x).is_corrupt tr
  );
  is_corrupt_later = (fun tr1 tr2 ->
    FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 label_is_corrupt_later)
  );
}

val is_corrupt_big_join:
  #a:Type ->
  tr:trace -> f:(a -> label) ->
  Lemma
  (is_corrupt tr (big_join f) <==> exists x. is_corrupt tr (f x))
  [SMTPat (is_corrupt tr (big_join f))]
let is_corrupt_big_join #a tr f =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%big_join) (big_join #a)

val big_join_eq:
  #a:Type ->
  tr:trace -> f:(a -> label) -> l:label ->
  Lemma
  (ensures l `can_flow tr` big_join f <==> (forall x. l `can_flow tr` f x))
  [SMTPat (l `can_flow tr` big_join f)]
let big_join_eq #a tr f l =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%big_join) (big_join #a)

val big_join_flow_to_component:
  #a:Type ->
  tr:trace -> f:(a -> label) -> x:a ->
  Lemma (big_join f `can_flow tr` (f x))
let big_join_flow_to_component #a tr f x =
  big_join_eq tr f (big_join f)
