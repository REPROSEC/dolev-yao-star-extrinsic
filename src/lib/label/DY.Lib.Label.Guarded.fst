module DY.Lib.Label.Guarded

open DY.Core
open DY.Lib.Event.Typed
open DY.Lib.Label.Event

#set-options "--fuel 0 --ifuel 0"

/// `guarded l g` is corrupt when `l` was corrupt before `g` was corrupt.

[@@"opaque_to_smt"]
val guarded:
  l:label -> g:label ->
  label
let guarded l g = mk_label {
  is_corrupt = (fun tr ->
    exists tr_before.
      tr_before <$ tr /\
      l.is_corrupt tr_before /\
      ~(g.is_corrupt tr_before)
  );
  is_corrupt_later = (fun tr1 tr2 -> ());
}

val is_corrupt_guarded:
  tr:trace ->
  l:label -> g:label ->
  Lemma (
    is_corrupt tr (guarded l g)
    <==> (
    exists tr_before.
      tr_before <$ tr /\
      is_corrupt tr_before l /\
      ~(is_corrupt tr_before g)
    )
  )
let is_corrupt_guarded tr l g =
  reveal_opaque (`%guarded) (guarded);
  reveal_opaque (`%is_corrupt) (is_corrupt);
  assert(forall (tr_before: trace_ unit).
    tr_before <$ (trace_forget_labels tr)
    ==>
    (fmap_trace_recover_before forget_label tr_before tr) <$ tr
  )

val guarded_secret:
  l:label ->
  Lemma (guarded l secret == l)
let guarded_secret l =
  intro_label_equal (guarded l secret) (l) (fun tr ->
    is_corrupt_guarded tr l secret
  )

val guarded_can_flow:
  tr:trace ->
  l1:label -> l2:label -> g1:label -> g2:label ->
  Lemma
  (requires forall tr. g2 `can_flow tr` g1 /\ l1 `can_flow tr` l2)
  (ensures guarded l1 g1 `can_flow tr` guarded l2 g2)
let guarded_can_flow tr l1 l2 g1 g2 =
  intro_can_flow tr (guarded l1 g1) (guarded l2 g2) (fun tr' ->
    is_corrupt_guarded tr' l1 g1;
    is_corrupt_guarded tr' l2 g2
  )

val is_corrupt_guarded_event:
  #a:Type0 -> {|event a|} ->
  tr:trace ->
  l:label -> prin:principal -> content:a ->
  Lemma
  (requires
    event_triggered tr prin content
  )
  (ensures
    is_corrupt tr (guarded l (event_triggered_label prin content))
    <==>
    is_corrupt (prefix tr (find_event_triggered_at_timestamp tr prin content)) l
  )
let is_corrupt_guarded_event #a #ev_a tr l prin content =
  is_corrupt_guarded tr l (event_triggered_label prin content);
  introduce is_corrupt tr (guarded l (event_triggered_label prin content)) ==> is_corrupt (prefix tr (find_event_triggered_at_timestamp tr prin content)) l with _. (
    eliminate
      exists tr_before.
        tr_before <$ tr /\
        is_corrupt tr_before l /\
        ~(is_corrupt tr_before (event_triggered_label prin content))
    returns is_corrupt (prefix tr (find_event_triggered_at_timestamp tr prin content)) l
    with _. (
      let ev_i = (find_event_triggered_at_timestamp tr prin content) in
      let tr_i = trace_length tr_before in
      if ev_i = tr_i then (
        reveal_opaque (`%grows) (grows #label);
        assert(prefix tr ev_i == tr_before)
      )
      else if ev_i < tr_i then (
        reveal_opaque (`%grows) (grows #label);
        assert(prefix tr (ev_i+1) <$ tr_before);
        reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
        is_corrupt_event_triggered_label tr_before prin content;
        assert(False)
      ) else (
        reveal_opaque (`%grows) (grows #label);
        assert(tr_before <$ prefix tr ev_i)
      )
    )
  );
  introduce is_corrupt (prefix tr (find_event_triggered_at_timestamp tr prin content)) l ==> is_corrupt tr (guarded l (event_triggered_label prin content)) with _. (
    let tr_before = (prefix tr (find_event_triggered_at_timestamp tr prin content)) in
    is_corrupt_event_triggered_label tr_before prin content
  )

/// A typical use-case of `guarded` is as follows:
/// - `l` is the label of an authentication key (e.g. signature key)
/// - `g` is an (or a join of) event label
///
/// In that scenario, when `g` is corrupt (i.e. the event has been triggered)
/// then consider the following traces:
///
/// <---------------> tr_before_ev, the trace on which the event predicate holds
/// <------------------> tr_ev, the smallest trace for which `g` is corrupt
/// <-------------------------> tr, the current trace
/// . . . . . . . . . ev . . .
///
/// In that case, we deduce that
/// either `l` has been corrupt in `tr_before_ev`
/// (in that case, `guarded l g` is corrupt),
/// or that an authentication predicate holds on `tr_before_ev`.
///
/// To prove `event_pred_lemma` and `auth_pred_lemma`,
/// if you know that `trace_invariant tr`,
/// you can deduce `trace_invariant tr_ev`
/// using the lemma `trace_invariant_before tr_ev tr`.

val guarded_authentication_lemma:
  tr:trace ->
  l:label -> g:label ->
  event_pred:(trace -> prop) ->
  event_pred_lemma:(tr_ev:trace{tr_ev <$ tr /\ is_corrupt tr_ev g} -> squash (exists i. i < trace_length tr_ev /\ event_pred (prefix tr_ev i))) ->
  auth_pred:(trace -> prop) ->
  auth_pred_lemma:(tr_before_ev:trace{tr_before_ev <$ tr /\ event_pred tr_before_ev} -> squash (is_corrupt tr_before_ev l \/ auth_pred tr_before_ev)) ->
  Lemma
  (requires is_corrupt tr g)
  (ensures
    is_corrupt tr (guarded l g) \/ (
      exists tr_before_ev.
        ~(is_corrupt tr_before_ev g) /\
        tr_before_ev <$ tr /\
        auth_pred tr_before_ev
    )
  )
let guarded_authentication_lemma tr l g event_pred event_pred_lemma auth_pred auth_pred_lemma =
  introduce ~(is_corrupt tr (guarded l g)) ==> exists tr_before_ev. ~(is_corrupt tr_before_ev g) /\ tr_before_ev <$ tr /\ auth_pred tr_before_ev with _. (
    exists_minimal_corrupt_trace_for_label tr g;
    eliminate exists tr_ev. tr_ev <$ tr /\ is_minimal_corrupt_trace_for_label g tr_ev
    returns _
    with _. (
      event_pred_lemma tr_ev;
      eliminate exists i. i < trace_length tr_ev /\ event_pred (prefix tr_ev i)
      returns _
      with _. (
        let tr_before_ev = prefix tr_ev i in
        is_corrupt_guarded tr_ev l g;
        auth_pred_lemma tr_before_ev
      )
    )
  )
