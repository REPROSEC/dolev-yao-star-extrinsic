module DY.Core.Internal.Ord

open FStar.List.Tot

/// This module defines a typeclass `integer_encodable`,
/// for types that can be (injectively) encoded as a list of integers,
/// and defines a total order `is_less_than` for instances of this typeclass.
///
/// This will be useful to define an order on `bytes` terms,
/// to normalize cryptographic functions that feature commutativity properties
/// (such as Diffie-Hellman or XOR).

class integer_encodable (t:Type) = {
  encode: t -> list int;
  encode_inj: x:t -> y:t -> Lemma
    (requires encode x == encode y)
    (ensures x == y)
  ;
}

val encode_inj_forall:
  t:Type -> {|integer_encodable t|} ->
  unit ->
  Lemma
  (forall (x:t) (y:t). encode x == encode y ==> x == y)
let encode_inj_forall t #ie () =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (encode_inj #t))

val is_less_than_aux:
  list int -> list int ->
  bool
let rec is_less_than_aux x y =
  match x, y with
  | [], [] -> true
  | [], hy::ty -> true
  | hx::tx, [] -> false
  | hx::tx, hy::ty ->
    hx < hy || (hx = hy && is_less_than_aux tx ty)

val is_less_than:
  #t:Type -> {|integer_encodable t|} ->
  t -> t ->
  bool
let is_less_than #t #ie x y =
  is_less_than_aux (encode x) (encode y)

val is_less_than_aux_total:
  x:list int -> y:list int ->
  Lemma (x `is_less_than_aux` y \/ y `is_less_than_aux` x)
let rec is_less_than_aux_total x y =
  match x, y with
  | [], [] -> ()
  | hx::tx, [] -> ()
  | [], hy::ty -> ()
  | hx::tx, hy::ty -> is_less_than_aux_total tx ty

val is_less_than_aux_refl:
  x:list int ->
  Lemma (x `is_less_than_aux` x)
let rec is_less_than_aux_refl x =
  match x with
  | [] -> ()
  | hx::tx -> is_less_than_aux_refl tx

val is_less_than_aux_trans:
  x:list int -> y:list int -> z:list int ->
  Lemma
  (requires x `is_less_than_aux` y /\ y `is_less_than_aux` z)
  (ensures x `is_less_than_aux` z)
let rec is_less_than_aux_trans x y z =
  match x, y, z with
  | [], _ , _ -> ()
  | hx::tx, [], _ -> ()
  | hx::tx, hy::ty, [] -> ()
  | hx::tx, hy::ty, hz::tz ->
    if hx = hy && hy = hz then
      is_less_than_aux_trans tx ty tz
    else ()

val is_less_than_aux_antisym:
  x:list int -> y:list int ->
  Lemma
  (requires x `is_less_than_aux` y /\ y `is_less_than_aux` x)
  (ensures x == y)
let rec is_less_than_aux_antisym x y =
  match x, y with
  | [], [] -> ()
  | hx::tx, [] -> assert(False)
  | [], hy::ty -> assert(False)
  | hx::tx, hy::ty ->
    is_less_than_aux_antisym tx ty

val is_less_than_total:
  #t:Type -> {|integer_encodable t|} ->
  x:t -> y:t ->
  Lemma (x `is_less_than` y \/ y `is_less_than` x)
let is_less_than_total x y =
  is_less_than_aux_total (encode x) (encode y)

val is_less_than_refl:
  #t:Type -> {|integer_encodable t|} ->
  x:t ->
  Lemma (x `is_less_than` x)
let is_less_than_refl x =
  is_less_than_aux_refl (encode x)

val is_less_than_trans:
  #t:Type -> {|integer_encodable t|} ->
  x:t -> y:t -> z:t ->
  Lemma
  (requires x `is_less_than` y /\ y `is_less_than` z)
  (ensures x `is_less_than` z)
let is_less_than_trans x y z =
  is_less_than_aux_trans (encode x) (encode y) (encode z)

val is_less_than_antisym:
  #t:Type -> {|integer_encodable t|} ->
  x:t -> y:t ->
  Lemma
  (requires x `is_less_than` y /\ y `is_less_than` x)
  (ensures x == y)
let is_less_than_antisym x y =
  is_less_than_aux_antisym (encode x) (encode y);
  encode_inj x y

instance integer_encodable_list_int: integer_encodable (list int) = {
  encode = (fun x -> x);
  encode_inj = (fun x y -> ());
}

val encode_pair:
  #t1:Type -> #t2:Type ->
  {|integer_encodable t1|} -> {|integer_encodable t2|} ->
  t1 -> t2 ->
  list int
let encode_pair x1 x2 =
  let l1 = encode x1 in
  let l2 = encode x2 in
  (List.Tot.length l1)::l1@l2

val encode_pair_inj:
  #t1:Type -> #t2:Type ->
  {|integer_encodable t1|} -> {|integer_encodable t2|} ->
  x1:t1 -> x2:t2 ->
  y1:t1 -> y2:t2 ->
  Lemma
  (requires encode_pair x1 x2 == encode_pair y1 y2)
  (ensures x1 == y1 /\ x2 == y2)
let encode_pair_inj x1 x2 y1 y2 =
  List.Tot.Properties.append_length_inv_head (encode x1) (encode x2) (encode y1) (encode y2);
  encode_inj x1 y1;
  encode_inj x2 y2

val encode_list:
  #t:Type ->
  {|integer_encodable t|} ->
  list t ->
  list int
let encode_list l =
  List.Tot.fold_right encode_pair (List.Tot.map encode l) []

val encode_list_inj:
  #t:Type ->
  {|integer_encodable t|} ->
  x:list t -> y:list t ->
  Lemma
  (requires encode_list x == encode_list y)
  (ensures x == y)
let rec encode_list_inj x y =
  match x, y with
  | [], [] -> ()
  | hx::tx, [] -> assert(False)
  | [], hy::ty -> assert(False)
  | hx::tx, hy::ty ->
    encode_pair_inj hx (encode_list tx) hy (encode_list ty);
    encode_list_inj tx ty

instance integer_encodable_list (t:Type) {|integer_encodable t|}: integer_encodable (list t) = {
  encode = encode_list;
  encode_inj = encode_list_inj;
}

instance integer_encodable_nat: integer_encodable nat = {
  encode = (fun (x:nat) -> [x]);
  encode_inj = (fun x y -> ());
}

instance integer_encodable_u8: integer_encodable FStar.UInt8.t = {
  encode = (fun x -> [FStar.UInt8.v x]);
  encode_inj = (fun x y -> ());
}

instance integer_encodable_u32: integer_encodable FStar.UInt32.t = {
  encode = (fun x -> [FStar.UInt32.v x]);
  encode_inj = (fun x y -> ());
}

instance integer_encodable_seq (t:Type) {|integer_encodable t|}: integer_encodable (Seq.seq t) = {
  encode = (fun x -> encode (Seq.seq_to_list x));
  encode_inj = (fun x y ->
    assert(Seq.seq_of_list (Seq.seq_to_list x) == x);
    assert(Seq.seq_of_list (Seq.seq_to_list y) == y);
    encode_inj (Seq.seq_to_list x) (Seq.seq_to_list y)
  );
}

instance integer_encodable_char: integer_encodable FStar.Char.char = {
  encode = (fun x ->
    encode (FStar.Char.u32_of_char x <: FStar.UInt32.t)
  );
  encode_inj = (fun x y ->
    encode_inj (FStar.Char.u32_of_char x <: FStar.UInt32.t) (FStar.Char.u32_of_char y <: FStar.UInt32.t)
  );
}

instance integer_encodable_string: integer_encodable string = {
  encode = (fun x ->
    encode (FStar.String.list_of_string x)
  );
  encode_inj = (fun x y ->
    FStar.String.string_of_list_of_string x;
    FStar.String.string_of_list_of_string y;
    encode_inj (FStar.String.list_of_string x) (FStar.String.list_of_string y)
  );
}
