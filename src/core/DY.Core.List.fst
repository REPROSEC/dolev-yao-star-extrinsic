module DY.Core.List

module List = FStar.List.Tot.Base
module ListProp = FStar.List.Tot.Properties


(*** Helper Lemmas on Lists ***)

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


(*** Reversed Lists ***)

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


let memP_singleton (#a:Type) (x: a) (y:a):
  Lemma
  ( y `memP` (Snoc Nil x) ==> x == y
  )
  = normalize_term_spec (memP #a)



let forall_rev_list (#a:Type) (xs: rev_list a) (p: a -> prop) : prop =
  forall x. x `memP` xs ==> p x
