module DY.Core.Attacker.Knowledge.Kleene

#set-options "--fuel 1 --ifuel 0"

/// This module formalizes Kleene's fixpoint theorem
/// https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem

type set_t (a:Type) = a -> prop

val is_subset:
  #a:Type ->
  set_t a -> set_t a ->
  prop
let is_subset #a set1 set2 =
  forall x. set1 x ==> set2 x

val is_equal:
  #a:Type ->
  set_t a -> set_t a ->
  prop
let is_equal #a set1 set2 =
  is_subset set1 set2 /\
  is_subset set2 set1

noeq
type directed_chain_t (a:Type) = {
  sets: nat -> set_t a;
  sets_monotonic:
    i:nat -> j:nat ->
    Lemma
    (requires i <= j)
    (ensures is_subset (sets i) (sets j))
  ;
}

val union_set:
  #a:Type ->
  (nat -> set_t a) ->
  set_t a
let union_set #a sets =
  fun x ->
    exists n. sets n x

val map_sets:
  #a:Type ->
  (set_t a -> set_t a) ->
  (nat -> set_t a) ->
  (nat -> set_t a)
let map_sets #a f sets =
  fun n -> fun x ->
    f (sets n) x

noeq
type f_properties (#a:Type) (f:set_t a -> set_t a) = {
  is_scott_continuous:
    chain:directed_chain_t a -> x:a ->
    Lemma (f (union_set chain.sets) x <==> union_set (map_sets f chain.sets) x)
  ;
  // scott continuity implies monotonicity,
  // but proving so requires extensionality on sets,
  // so instead we ask the user to prove it manually
  is_monotonic:
    set1:set_t a -> set2:set_t a ->
    Lemma
    (requires is_subset set1 set2)
    (ensures is_subset (f set1) (f set2))
  ;
}

val mk_weakest_fixpoint_aux:
  #a:Type ->
  (set_t a -> set_t a) -> nat ->
  set_t a
let rec mk_weakest_fixpoint_aux #a f n =
  fun x ->
    if n = 0 then (
      False
    ) else (
      f (mk_weakest_fixpoint_aux f (n-1)) x
    )

val mk_weakest_fixpoint:
  #a:Type ->
  (set_t a -> set_t a) ->
  set_t a
let mk_weakest_fixpoint #a f =
  union_set (mk_weakest_fixpoint_aux f)

val mk_weakest_fixpoint_aux_is_monotonic_consecutive:
  #a:Type ->
  f:(set_t a -> set_t a) -> f_properties f ->
  i:nat ->
  Lemma (is_subset (mk_weakest_fixpoint_aux f i) (mk_weakest_fixpoint_aux f (i+1)))
let rec mk_weakest_fixpoint_aux_is_monotonic_consecutive #a f f_props i =
  if i = 0 then ()
  else (
    mk_weakest_fixpoint_aux_is_monotonic_consecutive f f_props (i-1);
    f_props.is_monotonic (mk_weakest_fixpoint_aux f (i-1)) (mk_weakest_fixpoint_aux f i)
  )

val mk_weakest_fixpoint_aux_is_monotonic:
  #a:Type ->
  f:(set_t a -> set_t a) -> f_properties f ->
  i:nat -> j:nat ->
  Lemma
  (requires i <= j)
  (ensures is_subset (mk_weakest_fixpoint_aux f i) (mk_weakest_fixpoint_aux f j))
let rec mk_weakest_fixpoint_aux_is_monotonic #a f f_properties i j =
  if i = j then ()
  else (
    mk_weakest_fixpoint_aux_is_monotonic f f_properties i (j-1);
    mk_weakest_fixpoint_aux_is_monotonic_consecutive f f_properties (j-1)
  )

val mk_weakest_fixpoint_is_fixpoint:
  #a:Type ->
  f:(set_t a -> set_t a) ->
  f_properties f ->
  Lemma (
    is_subset (f (mk_weakest_fixpoint f)) (mk_weakest_fixpoint f) /\
    is_subset (mk_weakest_fixpoint f) (f (mk_weakest_fixpoint f))
  )
let mk_weakest_fixpoint_is_fixpoint #a f f_props =
  introduce forall x. f (mk_weakest_fixpoint f) x <==> mk_weakest_fixpoint f x
  with (
    f_props.is_scott_continuous {
      sets = mk_weakest_fixpoint_aux f;
      sets_monotonic = mk_weakest_fixpoint_aux_is_monotonic f f_props;
    } x;
    assert(forall n. f (mk_weakest_fixpoint_aux f n) x <==> mk_weakest_fixpoint_aux f (n+1) x)
  )

val mk_weakest_fixpoint_is_weakest_aux:
  #a:Type ->
  f:(set_t a -> set_t a) -> f_properties f ->
  set:set_t a ->
  n:nat ->
  Lemma
  (requires is_subset (f set) set)
  (ensures is_subset (mk_weakest_fixpoint_aux f n) set)
let rec mk_weakest_fixpoint_is_weakest_aux #a f f_props set n =
  if n = 0 then ()
  else (
    mk_weakest_fixpoint_is_weakest_aux f f_props set (n-1);
    f_props.is_monotonic (mk_weakest_fixpoint_aux f (n-1)) set
  )

val mk_weakest_fixpoint_is_weakest:
  #a:Type ->
  f:(set_t a -> set_t a) -> f_properties f ->
  set:set_t a ->
  Lemma
  (requires is_subset (f set) set)
  (ensures is_subset (mk_weakest_fixpoint f) set)
let mk_weakest_fixpoint_is_weakest #a f f_props set =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (mk_weakest_fixpoint_is_weakest_aux f f_props set))
