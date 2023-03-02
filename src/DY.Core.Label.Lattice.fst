module DY.Core.Label.Lattice

#set-options "--fuel 1 --ifuel 1"

noeq
type order (a:Type) = {
  rel: a -> a -> prop;
  refl: x:a -> Lemma (rel x x);
  trans: x:a -> y:a -> z:a -> Lemma (requires rel x y /\ rel y z) (ensures rel x z);
}

type lattice (a:Type) =
  | Leaf: a -> lattice a
  | Join: lattice a -> lattice a -> lattice a
  | Meet: lattice a -> lattice a -> lattice a

//val lattice_order: #a:Type -> order a -> lattice a -> lattice a -> prop
//let rec lattice_order #a ord x y =
//  match x, y with
//  | Leaf x0, Leaf y0 -> ord.rel x0 y0
//  | Join x1 x2, Leaf _ -> lattice_order ord x1 y /\ lattice_order ord x2 y
//  | Meet x1 x2, Leaf _ -> lattice_order ord x1 y \/ lattice_order ord x2 y
//  | Leaf _, Join y1 y2 -> lattice_order ord x y1 \/ lattice_order ord x y2
//  | Leaf _, Meet y1 y2 -> lattice_order ord x y1 /\ lattice_order ord x y2
//  | Join x1 x2, Join y1 y2 -> (lattice_order ord x1 y /\ lattice_order ord x2 y) \/ (lattice_order ord x y1 \/ lattice_order ord x y2)
//  | Join x1 x2, Meet y1 y2 -> (lattice_order ord x1 y /\ lattice_order ord x2 y) \/ (lattice_order ord x y1 /\ lattice_order ord x y2)
//  | Meet x1 x2, Join y1 y2 -> (lattice_order ord x1 y \/ lattice_order ord x2 y) \/ (lattice_order ord x y1 \/ lattice_order ord x y2)
//  | Meet x1 x2, Meet y1 y2 -> (lattice_order ord x1 y \/ lattice_order ord x2 y) \/ (lattice_order ord x y1 /\ lattice_order ord x y2)

val lattice_order: #a:Type -> order a -> lattice a -> lattice a -> prop
let rec lattice_order #a ord x y =
  match x, y with
  | Leaf x0, Leaf y0 -> ord.rel x0 y0
  | _, _ -> (
    let x_order =
      match x with
      | Leaf _ -> False
      | Join x1 x2 -> lattice_order ord x1 y /\ lattice_order ord x2 y
      | Meet x1 x2 -> lattice_order ord x1 y \/ lattice_order ord x2 y
    in
    let y_order =
      match y with
      | Leaf _ -> False
      | Join y1 y2 -> lattice_order ord x y1 \/ lattice_order ord x y2
      | Meet y1 y2 -> lattice_order ord x y1 /\ lattice_order ord x y2
    in
    x_order \/ y_order
  )

val meet_eq:
  #a:Type -> ord:order a ->
  x:lattice a -> y1:lattice a -> y2:lattice a ->
  Lemma
  (ensures (x `lattice_order ord` (Meet y1 y2)) <==> (x `lattice_order ord` y1 /\ x `lattice_order ord` y2))
let rec meet_eq #a ord x y1 y2 =
  match x with
  | Leaf _ -> ()
  | Join x1 x2 -> (
    meet_eq ord x1 y1 y2;
    meet_eq ord x2 y1 y2
  )
  | Meet x1 x2 -> (
    meet_eq ord x1 y1 y2;
    meet_eq ord x2 y1 y2
  )

val join_eq:
  #a:Type -> ord:order a ->
  x1:lattice a -> x2:lattice a -> y:lattice a ->
  Lemma
  (((Join x1 x2) `lattice_order ord` y) <==> (x1 `lattice_order ord` y /\ x2 `lattice_order ord` y))
let rec join_eq #a ord x1 x2 y =
  match y with
  | Leaf _ -> ()
  | Join y1 y2 -> (
    join_eq ord x1 x2 y1;
    join_eq ord x1 x2 y2
  )
  | Meet y1 y2 -> (
    join_eq ord x1 x2 y1;
    join_eq ord x1 x2 y2
  )

val leaf_eq:
  #a:Type -> ord:order a ->
  x:a -> y:a ->
  Lemma
  ((Leaf x) `lattice_order ord` (Leaf y) <==> x `ord.rel` y)
let leaf_eq #a ord x y = ()

val bottom_to_bottom:
  #a:Type -> ord:order a ->
  bottom:a -> x:lattice a ->
  Lemma
  (requires forall z. bottom `ord.rel` z)
  (ensures (Leaf bottom) `lattice_order ord` x)
let rec bottom_to_bottom #a ord bottom x =
  match x with
  | Leaf _ -> ()
  | Join x1 x2 -> (
    bottom_to_bottom ord bottom x1;
    bottom_to_bottom ord bottom x2
  )
  | Meet x1 x2 -> (
    bottom_to_bottom ord bottom x1;
    bottom_to_bottom ord bottom x2
  )

val top_to_top:
  #a:Type -> ord:order a ->
  top:a -> x:lattice a ->
  Lemma
  (requires forall z. z `ord.rel` top)
  (ensures x `lattice_order ord` (Leaf top))
let rec top_to_top #a ord top x =
  match x with
  | Leaf _ -> ()
  | Join x1 x2 ->
    top_to_top ord top x1;
    top_to_top ord top x2
  | Meet x1 x2 ->
    top_to_top ord top x1;
    top_to_top ord top x2

#push-options "--fuel 2"
val lattice_order_refl:
  #a:Type -> ord:order a ->
  x:lattice a ->
  Lemma (lattice_order ord x x)
let rec lattice_order_refl #a ord x =
  match x with
  | Leaf x0 -> ord.refl x0
  | Join x1 x2 ->
    lattice_order_refl ord x1;
    lattice_order_refl ord x2
  | Meet x1 x2 ->
    lattice_order_refl ord x1;
    lattice_order_refl ord x2
#pop-options

val lattice_order_monotone:
  #a:Type ->
  ord1:order a -> ord2:order a ->
  x:lattice a -> y:lattice a ->
  Lemma
  (requires (forall x0 y0. ord1.rel x0 y0 ==> ord2.rel x0 y0))
  (ensures lattice_order ord1 x y ==> lattice_order ord2 x y)
let rec lattice_order_monotone #a ord1 ord2 x y =
  match x, y with
  | Leaf x0, Leaf y0 -> ()
  | Join x1 x2, Leaf _
  | Meet x1 x2, Leaf _ ->
    lattice_order_monotone ord1 ord2 x1 y;
    lattice_order_monotone ord1 ord2 x2 y
  | Leaf _, Join y1 y2
  | Leaf _, Meet y1 y2 ->
    lattice_order_monotone ord1 ord2 x y1;
    lattice_order_monotone ord1 ord2 x y2
  | Meet x1 x2, Join y1 y2
  | Meet x1 x2, Meet y1 y2
  | Join x1 x2, Meet y1 y2
  | Join x1 x2, Join y1 y2 ->
    lattice_order_monotone ord1 ord2 x1 y;
    lattice_order_monotone ord1 ord2 x2 y;
    lattice_order_monotone ord1 ord2 x y1;
    lattice_order_monotone ord1 ord2 x y2

#push-options "--z3rlimit 10"
val lattice_order_trans:
  #a:Type -> ord:order a ->
  x:lattice a -> y:lattice a -> z:lattice a ->
  Lemma
  (ensures lattice_order ord x y /\ lattice_order ord y z ==> lattice_order ord x z)
let rec lattice_order_trans #a ord x y z =
  match x, y, z with
  | Leaf x0, Leaf y0, Leaf z0 ->
    FStar.Classical.move_requires_3 ord.trans x0 y0 z0
  | Join x1 x2, Leaf _, Leaf _
  | Meet x1 x2, Leaf _, Leaf _ ->
    lattice_order_trans ord x1 y z;
    lattice_order_trans ord x2 y z
  | Leaf _, Join y1 y2, Leaf _
  | Leaf _, Meet y1 y2, Leaf _ ->
    lattice_order_trans ord x y1 z;
    lattice_order_trans ord x y2 z
  | Leaf _, Leaf _, Join z1 z2
  | Leaf _, Leaf _, Meet z1 z2 ->
    lattice_order_trans ord x y z1;
    lattice_order_trans ord x y z2
  | Join x1 x2, Join y1 y2, Leaf _
  | Join x1 x2, Meet y1 y2, Leaf _
  | Meet x1 x2, Join y1 y2, Leaf _
  | Meet x1 x2, Meet y1 y2, Leaf _ ->
    lattice_order_trans ord x y1 z;
    lattice_order_trans ord x y2 z;
    lattice_order_trans ord x1 y z;
    lattice_order_trans ord x2 y z
  | Join x1 x2, Leaf _, Join z1 z2
  | Join x1 x2, Leaf _, Meet z1 z2
  | Meet x1 x2, Leaf _, Join z1 z2
  | Meet x1 x2, Leaf _, Meet z1 z2 ->
    lattice_order_trans ord x y z1;
    lattice_order_trans ord x y z2;
    lattice_order_trans ord x1 y z;
    lattice_order_trans ord x2 y z
  | Leaf _, Join y1 y2, Join z1 z2
  | Leaf _, Join y1 y2, Meet z1 z2
  | Leaf _, Meet y1 y2, Join z1 z2
  | Leaf _, Meet y1 y2, Meet z1 z2 ->
    lattice_order_trans ord x y z1;
    lattice_order_trans ord x y z2;
    lattice_order_trans ord x y1 z;
    lattice_order_trans ord x y2 z
  | Join x1 x2, Join y1 y2, Join z1 z2
  | Join x1 x2, Join y1 y2, Meet z1 z2
  | Join x1 x2, Meet y1 y2, Join z1 z2
  | Join x1 x2, Meet y1 y2, Meet z1 z2
  | Meet x1 x2, Join y1 y2, Join z1 z2
  | Meet x1 x2, Join y1 y2, Meet z1 z2
  | Meet x1 x2, Meet y1 y2, Join z1 z2
  | Meet x1 x2, Meet y1 y2, Meet z1 z2 ->
    lattice_order_trans ord x y z1;
    lattice_order_trans ord x y z2;
    lattice_order_trans ord x y1 z;
    lattice_order_trans ord x y2 z;
    lattice_order_trans ord x1 y z;
    lattice_order_trans ord x2 y z
#pop-options

val leaf_less_join:
  #a:Type -> ord:order a ->
  x:a -> y1:lattice a -> y2:lattice a ->
  Lemma
  (lattice_order ord (Leaf x) (Join y1 y2) <==> lattice_order ord (Leaf x) y1 \/ lattice_order ord (Leaf x) y2)
let leaf_less_join #a ord x y1 y2 = ()

val leaf_less_meet:
  #a:Type -> ord:order a ->
  x:a -> y1:lattice a -> y2:lattice a ->
  Lemma
  (lattice_order ord (Leaf x) (Meet y1 y2) <==> lattice_order ord (Leaf x) y1 /\ lattice_order ord (Leaf x) y2)
let leaf_less_meet #a ord x y1 y2 = ()
