module DY.Lib.Labels.DynamicLabel

open DY.Core

#set-options "--fuel 0 --ifuel 0"

(**
This is an attempt at introducing ordered guarded labels to implement some generic dynamically expanding label, that is corrupt if and only if a reveal event has occurred to some principal and a subsequent corruption of that principal has occurred.

This doesn't allow particularly fine-grained corruption, but was a first attempt at producing some kind of dynamic labels in a simple manner.
**)

(*** Ordered Guard ***)

/// 'ordered_guard l g' is corrupt when 'l' was corrupt and subsequently 'g' is corrupt
val ordered_guard :
  label ->
  label ->
  label
let ordered_guard l g = mk_label {
  is_corrupt = (fun tr ->
    exists tr_before tr_before_that.
      tr_before_that <$ tr_before /\
      tr_before <$ tr /\
      l.is_corrupt tr_before_that /\
      g.is_corrupt tr_before
  );
  is_corrupt_later = (fun tr1 tr2 -> ());
}

val is_corrupt_ordered_guard :
  tr:trace ->
  l:label -> g:label ->
  Lemma(
    is_corrupt tr (ordered_guard l g)
    <==> (
    exists tr_before tr_before_that.
      tr_before_that <$ tr_before /\
      tr_before <$ tr /\
      is_corrupt tr_before_that l /\
      is_corrupt tr_before g
    )
  )
let is_corrupt_ordered_guard tr l g =
  reveal_opaque(`%is_corrupt) (is_corrupt);
  assert(forall (tr_before: trace_ unit) (tr:trace).
    tr_before <$ (trace_forget_labels tr)
    ==>
    (fmap_trace_recover_before forget_label tr_before tr) <$ tr
  )

val ordered_guard_secret :
  l:label ->
  Lemma(ordered_guard l secret == secret)
let ordered_guard_secret l =
  introduce forall tr. ~(is_corrupt tr secret) with (
    reveal_opaque (`%is_corrupt) (is_corrupt);
    reveal_opaque (`%secret) (secret)
  );
  introduce forall tr. is_corrupt tr (ordered_guard l secret) <==> is_corrupt tr secret with (
    is_corrupt_ordered_guard tr l secret
  );
  intro_label_equal (ordered_guard l secret) (secret) (fun tr ->
    reveal_opaque (`%can_flow) (can_flow)
  )

val ordered_guard_public :
  g:label ->
  Lemma(ordered_guard public g == g)
let ordered_guard_public g =
  introduce forall tr. (is_corrupt tr public) with (
    reveal_opaque (`%is_corrupt) (is_corrupt);
    reveal_opaque (`%public) (public)
  );
  introduce forall tr. is_corrupt tr (ordered_guard public g) <==> is_corrupt tr g with (
    is_corrupt_ordered_guard tr public g;
    assert(is_corrupt tr (ordered_guard public g)
      <==> (
      exists tr_before.
        tr_before <$ tr /\
        is_corrupt tr_before g
    ))
  );
  intro_label_equal (ordered_guard public g) (g) (fun tr ->
    reveal_opaque (`%can_flow) (can_flow)
  )

val ordered_guard_l_is_corrupt_can_flow_to_g :
  tr:trace ->
  l:label ->
  g:label ->
  Lemma
  (requires is_corrupt tr l)
  (ensures ordered_guard l g `can_flow tr` g)
let ordered_guard_l_is_corrupt_can_flow_to_g tr l g =
  reveal_opaque (`%can_flow) (can_flow);
  reveal_opaque (`%is_corrupt) (is_corrupt)


val ordered_guard_can_flow :
  tr:trace ->
  l1:label -> l2:label -> g1:label -> g2:label ->
  Lemma
  (requires forall tr. g1 `can_flow tr` g2 /\ l1 `can_flow tr` l2)
  (ensures ordered_guard l1 g1 `can_flow tr` ordered_guard l2 g2)
let ordered_guard_can_flow tr l1 l2 g1 g2 =
  reveal_opaque (`%can_flow) (can_flow);
  introduce forall tr'. tr <$ tr' /\ is_corrupt tr' (ordered_guard l2 g2) ==> is_corrupt tr' (ordered_guard l1 g1) with (
    introduce _ ==> _ with _. (
      is_corrupt_ordered_guard tr' l1 g1;
      is_corrupt_ordered_guard tr' l2 g2
    )
  )

(*** Existentially Ordered Guard ***)

// ordered_guard but existentially quantified
val ordered_ex_guard :
  #a:Type ->
  (a -> label) ->
  (a -> label) ->
  label
let ordered_ex_guard #a f g = mk_label {
  is_corrupt = (fun tr ->
    exists tr_before tr_before_that.
      exists x.
        tr_before_that <$ tr_before /\
        tr_before <$ tr /\
        (f x).is_corrupt tr_before_that /\
        (g x).is_corrupt tr_before
  );
  is_corrupt_later = (fun tr1 tr2 -> ());
}


val is_corrupt_ordered_ex_guard :
  #a:Type ->
  tr:trace ->
  l:(a -> label) -> g:(a -> label) ->
  Lemma(
    is_corrupt tr (ordered_ex_guard l g)
    <==> (
    exists tr_before tr_before_that.
      exists x.
        tr_before_that <$ tr_before /\
        tr_before <$ tr /\
        is_corrupt tr_before_that (l x) /\
        is_corrupt tr_before (g x)
    )
  )
let is_corrupt_ordered_ex_guard #a tr l g =
  reveal_opaque(`%is_corrupt) (is_corrupt);
  assert(forall (tr_before: trace_ unit) (tr:trace).
    tr_before <$ (trace_forget_labels tr)
    ==>
    (fmap_trace_recover_before forget_label tr_before tr) <$ tr
  );
  assert(is_corrupt tr (ordered_ex_guard l g) ==>
    (exists tr_before tr_before_that.
       exists x.
        tr_before_that <$ tr_before /\
        tr_before <$ (trace_forget_labels tr) /\
        (l x).is_corrupt tr_before_that /\
        (g x).is_corrupt tr_before
    )
  )

val ordered_ex_guard_secret :
  #a:Type ->
  l:(a -> label) ->
  Lemma(
    let g a = secret in
    ordered_ex_guard l g == secret
  )
let ordered_ex_guard_secret #a l =
  let g a = secret in
  introduce forall tr. ~(is_corrupt tr secret) with (
    reveal_opaque (`%is_corrupt) (is_corrupt);
    reveal_opaque (`%secret) (secret)
  );
  introduce forall tr. is_corrupt tr (ordered_ex_guard l g) <==> is_corrupt tr secret with (
    is_corrupt_ordered_ex_guard tr l g
  );
  intro_label_equal (ordered_ex_guard l g) (secret) (fun tr ->
    reveal_opaque (`%can_flow) (can_flow)
  )


val ordered_ex_guard_eq_ordered_guard :
  #a:Type ->
  tr:trace -> f:(a -> label) -> g:(a -> label) -> l:label ->
  Lemma
  (ensures l `can_flow tr` ordered_ex_guard f g <==> (forall x. l `can_flow tr` ordered_guard (f x) (g x)))
let ordered_ex_guard_eq_ordered_guard #a tr f g l =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  reveal_opaque (`%can_flow) (can_flow)

val ordered_ex_guard_can_flow :
  #a:Type ->
  tr:trace ->
  l1:(a -> label) -> l2:(a -> label) -> g1:(a -> label) -> g2:(a -> label) ->
  Lemma
  (requires forall tr x. (g1 x) `can_flow tr` (g2 x) /\ (l1 x) `can_flow tr` (l2 x))
  (ensures forall x. ordered_ex_guard l1 g1 `can_flow tr` ordered_guard (l2 x) (g2 x))
let ordered_ex_guard_can_flow tr l1 l2 g1 g2 =
  reveal_opaque (`%can_flow) (can_flow);
  ordered_ex_guard_eq_ordered_guard tr l1 g1 (ordered_ex_guard l1 g1);
  ordered_ex_guard_eq_ordered_guard tr l2 g2 (ordered_ex_guard l2 g2);

  introduce forall x. ordered_guard (l1 x) (g1 x) `can_flow tr` ordered_guard (l2 x) (g2 x) with
    ordered_guard_can_flow tr (l1 x) (l2 x) (g1 x) (g2 x)


(*** Reveal event triggered label ***)

val reveal_event_triggered_label :
  timestamp -> principal -> label
let reveal_event_triggered_label ts prin = mk_label {
  is_corrupt = (fun tr ->
    reveal_event_triggered tr prin ts
  );
  is_corrupt_later = (fun tr1 tr2 -> ());
}

#push-options "--fuel 0 --ifuel 1"
val is_corrupt_reveal_event_triggered_label:
  tr:trace ->
  ts:timestamp -> prin:principal ->
  Lemma (
    is_corrupt tr (reveal_event_triggered_label ts prin)
    <==>
    reveal_event_triggered tr prin ts
  )
  [SMTPat (is_corrupt tr (reveal_event_triggered_label ts prin))]
let is_corrupt_reveal_event_triggered_label tr ts prin =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  FStar.Classical.forall_intro (get_entry_at_fmap_trace forget_label tr);
  assert(reveal_event_triggered tr prin ts <==> reveal_event_triggered (trace_forget_labels tr) prin ts)
#pop-options

(*** Reveal principal label ***)

// this label is corrupt if reveal_event is triggered then the principal_label is corrupt
val reveal_principal_label :
  timestamp ->
  label
let reveal_principal_label ts = ordered_ex_guard (reveal_event_triggered_label ts) principal_label


val reveal_principal_label_can_flow_to_principal_label :
  tr:trace ->
  prin:principal ->
  ts:timestamp ->
  Lemma
  (requires reveal_event_triggered tr prin ts)
  (ensures (
    reveal_principal_label ts `can_flow tr` (principal_label prin)
  ))
let reveal_principal_label_can_flow_to_principal_label tr prin ts =
  ordered_ex_guard_eq_ordered_guard tr (reveal_event_triggered_label ts) (principal_label) (reveal_principal_label ts);

  is_corrupt_reveal_event_triggered_label tr ts prin;

  ordered_guard_l_is_corrupt_can_flow_to_g tr (reveal_event_triggered_label ts prin) (principal_label prin)
