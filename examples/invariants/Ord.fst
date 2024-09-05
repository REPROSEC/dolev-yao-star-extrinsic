module Ord

/// The Ord Typeclass
/// -----------------
///
/// * total order defined by a "less or equal" operator ``leq_``
/// * containing proofs that ``leq_`` is a total order
///   (reflexivity ``refl``, totality ``total_``, anti-symmetry ``anti_symm``, transitivity ``trans`` )

class ord_leq (a:eqtype) =
  { leq_: a -> a -> bool
  ; refl: (x:a) -> Lemma (x `leq_` x)
  ; total_: (x:a) -> (y:a) -> Lemma (x `leq_` y \/ y `leq_` x)
  //; anti_symm: (x:a) -> (y:a) -> Lemma (x `leq_` y /\ y `leq_` x ==> x = y)
  ; trans: (x:a) -> (y:a) -> (z:a) ->  Lemma (x `leq_` y /\ y `leq_` z ==> x `leq_` z)
  }


/// comparison functions derived from ``leq_``
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// corresponding to "<", "<=", ">" and ">="

let lt (#a:eqtype){|ord_leq a|} (x y : a) : bool =
  match (leq_ x y, x = y) with
  | (true, false) -> true
  | _ -> false

let leq (#a:eqtype){|ord_leq a|} (x y : a) : bool = leq_ x y

let lt_implies_leq {|ord_leq 'a|} (x y : 'a) :
  Lemma 
  (requires x `lt` y)
  (ensures x `leq` y /\ x <> y)
  [SMTPat (x `lt` y)]
  = ()

let leq_is_lt_or_equal {|ord_leq 'a|} (x y : 'a) :
  Lemma
  (requires
     x `leq` y
  )
  (ensures
     x `lt` y
     \/ x = y
  )
  [SMTPat (x `leq` y)]
  = ()

/// the total order properties as separate lemmas
/// (needed for helpful SMTPats)

let reflexivity {|ord_leq 'a |} (x : 'a)
  : Lemma (x `leq` x)
    [SMTPat (x `leq` x)]
  = refl x

let totality {| ord_leq 'a |} (x y : 'a)
  : Lemma (x `leq` y \/ y `leq` x)
  [SMTPat (x `leq` y); SMTPat (y `leq` x)]
  = total_ x y

// let anti_symmetry #a {| oa: ord_leq a |} (x y : a)
//   : Lemma (x `leq` y /\ y `leq` x ==> x = y)
//   [SMTPat (leq #a #oa x  y)] //; SMTPat (y `leq` x)]
//  = anti_symm x y

let transitivity {| ord_leq 'a |} (x y z : 'a)
  : Lemma (x `leq` y /\ y `leq` z ==> x `leq` z)
  [SMTPat (x `leq` y); SMTPat (y `leq` z)]
  = trans x y z

let transitivity_forall #a {| ord_leq a |} unit
  : Lemma (forall (x y z : a). x `leq` y /\ y `leq` z ==> x `leq` z )
= ()

let transitivity_lt {| ord_leq 'a |} (x y z : 'a)
  : Lemma (x `lt` y /\ y `lt` z ==> x `lt` z)
  [SMTPat (x `lt` y); SMTPat (y `lt` z)]
  = admit()

let transitivity_leq_lt {|ord_leq 'a|} (x y z : 'a)
  : Lemma 
    (requires
       x `leq` y /\ y `lt` z
    )
    (ensures
       x `lt` z
    )
    = () 


let lt_not_eq {|ord_leq 'a|} (x y : 'a)
  : Lemma 
    (requires x `lt` y)
    (ensures x <> y)
    [SMTPat (x `lt` y)]
    = ()

let max {| ord_leq 'a |} (x y : 'a) =
  if x `leq` y then y else x

let max_is_largest {|ord_leq 'a|} (x y :'a) :
  Lemma (x `leq` max x y /\ y `leq` max x y)
  = ()

/// Instances
/// ---------

/// Int
/// ~~~

instance ord_leq_int : ord_leq int =
  { leq_ = (<=)
  ; refl = (fun _ -> ())
  ; total_ = (fun _ _ -> ())
  // ; anti_symm = (fun _ _ -> ())
  ; trans = (fun _ _ _ -> ())
  }

/// Nat
/// ~~~

instance ord_leq_nat : ord_leq nat =
  { leq_ = (<=)
  ; refl = (fun _ -> ())
  ; total_ = (fun _ _ -> ())
  // ; anti_symm = (fun _ _ -> ())
  ; trans = (fun _ _ _ -> ())
  }
