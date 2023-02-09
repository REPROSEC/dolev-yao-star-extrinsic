module DY.Label.Type

open DY.Label.Lattice

type principal = string

type pre_pre_label = principal

[@@"opaque_to_smt"]
val pre_pre_label_order: order pre_pre_label
let pre_pre_label_order = {
  rel = (fun x y -> x == y);
  refl = (fun x -> ());
  trans = (fun x y z -> ());
}

val corruption_pred_ok: #a:Type -> order a -> (a -> prop) -> prop
let corruption_pred_ok #a ord pred =
  forall x y. pred x /\ ord.rel x y ==> pred y

type corruption_pred (#a:Type) (ord:order a) =
  pred:(a -> prop){corruption_pred_ok ord pred}

type pre_label (a:Type) =
  | Secret: pre_label a
  | State: a -> pre_label a
  | Public: pre_label a

val pre_label_order: #a:Type -> ord:order a -> corruption_pred ord  -> order (pre_label a)
let pre_label_order ord is_corrupt = {
  rel = (fun x y ->
    match x, y with
    | Secret, _ -> True
    | _, Secret -> False
    | State px, State py -> is_corrupt py \/ ord.rel px py
    | State _, Public -> True
    | Public, Public -> True
    | Public, State py -> is_corrupt py
  );
  refl = (fun x ->
    match x with
    | State x0 -> ord.refl x0
    | _ -> ()
  );
  trans = (fun x y z ->
    match x, y, z with
    | State x0, State y0, State z0 -> FStar.Classical.move_requires_3 ord.trans x0 y0 z0
    | _, _, _ -> ()
  );
}

type label = lattice (pre_label pre_pre_label)

val label_order: corruption_pred pre_pre_label_order -> order label
let label_order is_corrupt = {
  rel = lattice_order (pre_label_order pre_pre_label_order is_corrupt);
  refl = (fun x ->
    lattice_order_refl (pre_label_order pre_pre_label_order is_corrupt) x
  );
  trans = (fun x y z ->
    lattice_order_trans (pre_label_order pre_pre_label_order is_corrupt) x y z
  );
}
