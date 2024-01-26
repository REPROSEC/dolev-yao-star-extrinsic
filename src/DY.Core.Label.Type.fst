module DY.Core.Label.Type

open DY.Core.Label.Lattice

type principal = string

type pre_pre_label (desc_t:Type0) =
  | P: prin:principal -> pre_pre_label desc_t
  | S: prin:principal -> serialized_description:desc_t -> pre_pre_label desc_t

val get_principal: #desc_t:Type0 -> pre_pre_label desc_t -> option principal
let get_principal #desc_t l =
  match l with
  | P p -> Some p
  | S p _ -> Some p

val get_description: #desc_t:Type0 -> pre_pre_label desc_t -> option desc_t
let get_description l =
  match l with
  | P _ -> None
  | S _ s -> Some s

val pre_pre_label_order: #desc_t:Type0 -> order desc_t -> order (pre_pre_label desc_t)
let pre_pre_label_order #desc_t description_order = {
  rel = (fun x y ->
    match x, y with
    | S px _, P py
    | P px, P py -> px == py
    | P _, S _ _ -> False
    | S px dx, S py dy ->
      px == py /\ description_order.rel dx dy
  );
  refl = (fun x ->
    match x with
    | S _ d -> description_order.refl d
    | _ -> ()
  );
  trans = (fun x y z ->
    match x, y, z with
    | S _ dx, S _ dy, S _ dz -> description_order.trans dx dy dz
    | _, _, _ -> ()
  );
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

type label (desc_t:Type0) = lattice (pre_label (pre_pre_label desc_t))

val label_order:
  #desc_t:Type0 ->
  desc_order:order desc_t -> corruption_pred (pre_pre_label_order desc_order) ->
  order (label desc_t)
let label_order #desc_t desc_order is_corrupt = {
  rel = lattice_order (pre_label_order (pre_pre_label_order desc_order) is_corrupt);
  refl = (fun x ->
    lattice_order_refl (pre_label_order (pre_pre_label_order desc_order) is_corrupt) x
  );
  trans = (fun x y z ->
    lattice_order_trans (pre_label_order (pre_pre_label_order desc_order) is_corrupt) x y z
  );
}
