module PreOrd

/// A Typeclass for a total Preorder
/// ---------------------------------
///
/// * preorder defined by a "less or equal" operator ``leq_``
/// * containing proofs that ``leq_`` is a total preorder
///   (reflexivity ``refl``, totality ``total_`` and  transitivity ``trans`` )

class preord_leq (a:eqtype) =
  { leq_: a -> a -> bool
  ; refl: (x:a) -> Lemma (x `leq_` x)
  ; total_: (x:a) -> (y:a) -> Lemma (x `leq_` y \/ y `leq_` x)
  ; trans: (x:a) -> (y:a) -> (z:a) ->  Lemma (x `leq_` y /\ y `leq_` z ==> x `leq_` z)
  }


/// comparison functions derived from ``leq_``
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// corresponding to "<", "<="

let lt (#a:eqtype){|preord_leq a|} (x y : a) : bool =
  match (leq_ x y, x = y) with
  | (true, false) -> true
  | _ -> false

let leq (#a:eqtype){|preord_leq a|} (x y : a) : bool = leq_ x y


/// the preorder properties as separate lemmas
/// (needed for helpful SMTPats)

let reflexivity {|preord_leq 'a |} (x : 'a)
  : Lemma (x `leq` x)
    [SMTPat (x `leq` x)]
  = refl x

let totality {|preord_leq 'a|} (x y:'a)
  : Lemma (x `leq` y \/ y `leq` x)
    [SMTPat (x `leq`y)]
    = total_ x y

let transitivity {| preord_leq 'a |} (x y z : 'a)
  : Lemma (x `leq` y /\ y `leq` z ==> x `leq` z)
  [SMTPat (x `leq` y); SMTPat (y `leq` z)]
  = trans x y z

let transitivity_forall #a {| preord_leq a |} unit
  : Lemma (forall (x y z : a). x `leq` y /\ y `leq` z ==> x `leq` z )
= ()


/// Properties

let lt_implies_leq {|preord_leq 'a|} (x y : 'a) :
  Lemma 
  (requires x `lt` y)
  (ensures x `leq` y /\ x <> y)
  [SMTPat (x `lt` y)]
  = ()

let leq_is_lt_or_equal {|preord_leq 'a|} (x y : 'a) :
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


let transitivity_lt {| preord_leq 'a |} (x y z : 'a)
  : Lemma (x `lt` y /\ y `lt` z ==> x `lt` z)
  [SMTPat (x `lt` y); SMTPat (y `lt` z)]
  = admit()

let transitivity_leq_lt {|preord_leq 'a|} (x y z : 'a)
  : Lemma 
    (requires
       x `leq` y /\ y `lt` z
    )
    (ensures
       x `lt` z
    )
    = () 


let lt_not_eq {|preord_leq 'a|} (x y : 'a)
  : Lemma 
    (requires x `lt` y)
    (ensures x <> y)
    [SMTPat (x `lt` y)]
    = ()

/// Maximum

let max {| preord_leq 'a |} (x y : 'a) =
  if x `leq` y then y else x

let max_is_largest {|preord_leq 'a|} (x y :'a) :
  Lemma (x `leq` max x y /\ y `leq` max x y)
  = ()

/// Instances
/// ---------

/// Int
/// ~~~

instance preord_leq_int : preord_leq int =
  { leq_ = (<=)
  ; refl = (fun _ -> ())
  ; total_ = (fun _ _ -> ())
  ; trans = (fun _ _ _ -> ())
  }

/// Nat
/// ~~~

instance preord_leq_nat : preord_leq nat =
  { leq_ = (<=)
  ; refl = (fun _ -> ())
  ; total_ = (fun _ _ -> ())
  ; trans = (fun _ _ _ -> ())
  }
