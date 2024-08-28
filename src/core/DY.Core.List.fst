module DY.Core.List

module List = FStar.List.Tot.Base
module ListProp = FStar.List.Tot.Properties

let rec choose_equals (#a #b:eqtype) (f g: a -> option b) (xs: list a):
  Lemma 
  ( requires
      forall x. x `List.mem` xs ==> f x = g x
  )
  (ensures
    List.choose f xs = List.choose g xs
  )
  = normalize_term_spec (List.choose #a #b);
    match xs with
    | [] -> ()
    | hd :: tl -> choose_equals f g tl

let rec mem_choose (#a #b:eqtype) (f: a -> option b) (xs : list a) (x:a):
  Lemma
  (requires 
     x `List.mem` xs /\ Some? (f x)
  )
  (ensures Some?.v (f x) `List.mem` (List.choose f xs)
  )
  = match xs with
  | [] -> ()
  | hd :: tl ->
      if hd = x
      then ()
      else mem_choose f tl x 


let rec mem_choose_elim (#a #b:eqtype) (f: a -> option b) (xs : list a) (y : b)
  : Lemma
  (ensures (
    y `List.mem` (List.choose f xs) ==> 
    (exists x. x `List.mem` xs /\ Some? (f x) /\ Some?.v (f x) = y)
    )
  )
  =match xs with
  | [] -> ()
  | hd :: tl -> mem_choose_elim f tl y


let pair_elem_fst_elem (#a #b:eqtype) (p:(a * b)) (xs: list (a*b)):
  Lemma
  ( p `List.mem` xs ==> fst p `List.mem` (List.map fst xs)
  )
  [SMTPat (p `List.mem` xs) ]
  = FStar.List.Tot.Properties.memP_map_intro fst p xs

// let rec index_is_mem (#a:eqtype) (xs:list a) (i:nat{i < List.length xs}):
//   Lemma(
//     (xs `List.index` i) `List.mem` xs
//   )
//   = match xs with
//   | [] -> ()
//   | hd::tl ->
//       if i = 0 
//       then ()
//       else index_is_mem tl ((i-1) <: nat)


// let rec mem_has_index (#a:eqtype) (xs: list a) (x:a):
//   Lemma
//   (requires
//     x `List.mem` xs
//   )
//   (ensures (exists i. x = List.index xs i)
//   )
//   = match xs with
//   | [] -> ()
//   | hd :: tl -> 
//     if hd = x 
//     then (
//       introduce exists i. x = List.index xs i
//       with 0
//       and ()
//     )
//     else ( 
//       mem_has_index tl x;
//       eliminate exists i. x = List.index tl i
//       returns (exists i. x = List.index xs i)
//       with _ .
//       ( introduce exists i. x = List.index xs i
//         with (i+1) and ()
//       )
//     )

// let distinct_mems_have_distinct_indices (#a:eqtype) (xs:list a) (x y : a):
//   Lemma
//   ( requires 
//       x <> y
//       /\ x `List.mem` xs /\ y `List.mem` xs
//   )
//   (ensures
//      exists i j. x = xs `List.index` i /\ y = xs `List.index` j /\ i <> j
//   )
//   = mem_has_index xs x;
//     mem_has_index xs y
    

// let rec xy (#a #b:eqtype) (f: a -> option b) (xs:list a) (y:a):
//   Lemma
//   (requires List.noRepeats xs
//     /\ (forall x x'. x <> x' /\ Some? (f x) /\ Some? (f x') ==> f x <> f x')
//     /\ Some? (f y)
//     /\ ~ (y `List.mem` xs)
//   )
//   (ensures (
//      let Some fy = f y in
//      ~ (fy `List.mem` (List.choose f xs))
//   )
//   )
// = let Some fy = f y in
//   match xs with
//   | [] -> ()
//   | hd::tl -> xy f tl y
      

// let rec choose_no_repeats (#a #b:eqtype) (f: a  -> option b) (xs:list a):
//   Lemma 
//   ( requires 
//       List.noRepeats xs
//       /\ (forall x y . x <> y /\ Some? (f x) /\ Some? (f y) ==>
//         f x <> f y)
//   )
//   (ensures List.noRepeats (List.choose f xs)
//   )
//   = match xs with
//  | [] -> ()
//  | hd :: tl ->
//      match f hd with
//      | Some x -> (
//          choose_no_repeats f tl;
//          xy f tl hd
//        )
//      | None -> choose_no_repeats f tl 


/// The trace is a list of trace events.
/// Because the trace grows with time and the time is often represented going from left to right,
/// the trace is actually a reversed list.
/// To avoid confusions, we define a custom inductive to swap the arguments of the "cons" constructor.

type rev_list (a:Type) =
  | Nil : rev_list a
  | Snoc: rev_list a -> a -> rev_list a

// membership of an elemnt in a reversed list (the same as List.memP)
let rec memP (#a:Type) (m:a) (xs:rev_list a) : prop =
  match xs with
  | Nil -> false
  | Snoc init last -> 
      last == m \/ memP m init

let forall_rev_list (#a:Type) (xs: rev_list a) (p: a -> prop) : prop =
  forall x. x `memP` xs ==> p x
