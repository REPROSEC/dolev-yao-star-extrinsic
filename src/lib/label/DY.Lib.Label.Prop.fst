module DY.Lib.Label.Prop

open DY.Core

#set-options "--fuel 0 --ifuel 0"

/// Interpret a proposition as a label:
/// it is always corrupt if the proposition is true,
/// otherwise it is never corrupt.
/// It may for example be useful in combination with `big_join`.

[@@"opaque_to_smt"]
val prop_to_label: prop -> label
let prop_to_label p = mk_label {
  is_corrupt = (fun tr -> p);
  is_corrupt_later = (fun tr1 tr2 -> ());
}

val is_corrupt_prop_to_label:
  tr:trace -> p:prop ->
  Lemma
  (is_corrupt tr (prop_to_label p) <==> p)
  [SMTPat (is_corrupt tr (prop_to_label p))]
let is_corrupt_prop_to_label tr p =
  reveal_opaque (`%prop_to_label) (prop_to_label);
  reveal_opaque (`%is_corrupt) (is_corrupt)

val prop_to_label_equal:
  p1:prop -> p2:prop ->
  Lemma
  (requires p1 <==> p2)
  (ensures prop_to_label p1 == prop_to_label p2)
let prop_to_label_equal p1 p2 =
  intro_label_equal (prop_to_label p1) (prop_to_label p2) (fun tr -> ())

val prop_to_label_true:
  p:prop ->
  Lemma
  (requires p)
  (ensures prop_to_label p == public)
let prop_to_label_true p =
  intro_label_equal (prop_to_label p) (public) (fun tr -> ())

val prop_to_label_false:
  p:prop ->
  Lemma
  (requires ~p)
  (ensures prop_to_label p == secret)
let prop_to_label_false p =
  intro_label_equal (prop_to_label p) (secret) (fun tr -> ())
