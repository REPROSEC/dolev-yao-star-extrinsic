module DY.Core.List

module List = FStar.List.Tot.Base

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


let rec mem_index (#a:eqtype) (xs: list a) (x:a):
  Lemma
  (requires
    x `List.mem` xs
  )
  (ensures (exists i. x = List.index xs i)
  )
  = match xs with
  | [] -> ()
  | hd :: tl -> 
    if hd = x 
    then (
      introduce exists i. x = List.index xs i
      with 0
      and ()
    )
    else ( 
      mem_index tl x;
      eliminate exists i. x = List.index tl i
      returns (exists i. x = List.index xs i)
      with _ .
      ( introduce exists i. x = List.index xs i
        with (i+1) and ()
      )
    )
