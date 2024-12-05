module DY.Core.Trace.SplitUtils.Derived

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.SplitUtils

/// This module contains derived functions and lemmas based on
/// trace arithmetic (trace_concat, trace_subtract).


/// Derived properties of trace arithmetic

let trace_subtract_nil (#label_t:Type) (tr:trace_ label_t)
  : Lemma
    ((tr <--> empty_trace) == tr)
    [SMTPat (tr <--> empty_trace)]
  = trace_concat_subtract empty_trace tr

let trace_subtract_itself (#label_t:Type) (tr:trace_ label_t)
  : Lemma
    ((tr <--> tr) == empty_trace)
    [SMTPat (tr <--> tr)]
  = trace_concat_subtract tr empty_trace

let trace_concat_snoc_right (#label_t:Type) (tr1 tr2:trace_ label_t) (e:trace_entry_ label_t)
  : Lemma
    (tr1 <++> (append_entry tr2 e) == append_entry (tr1 <++> tr2) e)
  = trace_concat_assoc tr1 tr2 (append_entry empty_trace e)

let trace_subtract_concat_left (#label_t:Type) (tr1 tr2 tr3:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2)
    (ensures ((tr2 <--> tr1) <++> tr3) == ((tr2 <++> tr3) <--> tr1))
  = trace_concat_assoc tr1 (tr2 <--> tr1) tr3

let trace_subtract_concat_slices (#label_t:Type) (tr1 tr2 tr3:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2 /\ tr2 <$ tr3)
    (ensures (tr3 <--> tr1) == ((tr2 <--> tr1) <++> (tr3 <--> tr2)))
    [SMTPat ((tr2 <--> tr1) <++> (tr3 <--> tr2))]
  = trace_subtract_concat_left tr1 tr2 (tr3 <--> tr2);
    trace_subtract_concat tr2 tr3


/// Splitting a trace at a particular timestamp, getting the entry at that timestamp,
/// along with the prefix before and suffix after that timestamp.
/// Derived from trace subtraction.

let trace_split (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts `on_trace` tr})
  : (trace_ label_t & trace_entry_ label_t & trace_ label_t)
  = let tr1_e = prefix tr (ts + 1) in
    (init tr1_e, last tr1_e, tr <--> tr1_e)

/// Properties of trace splitting

let trace_split_trace_length (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts `on_trace` tr})
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
      trace_length tr1 = ts /\ trace_length tr2 = (trace_length tr) - ts - 1
    )
    [SMTPat (trace_split tr ts)]
  = ()

let trace_split_get_entry (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts `on_trace` tr}) (i:timestamp{i `on_trace` tr})
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
      get_entry_at tr i == (
        if i < ts then get_entry_at tr1 i
        else if i = ts then e
        else get_entry_at tr2 (i - ts - 1)
      )
    )
  = let (tr1, e, tr2) = trace_split tr ts in
    if i < ts then prefix_prefix_eq tr1 (prefix tr (ts + 1)) ts
    else if i = ts then ()
    else trace_subtract_get_entry (append_entry tr1 e) tr i

let trace_split_fmap (#a #b:Type) (tr:trace_ a) (ts:timestamp{ts `on_trace` tr}) (f:a -> b)
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
      let (tr1', e', tr2') = trace_split (fmap_trace f tr) ts in
      fmap_trace f tr1 == tr1' /\
      fmap_trace_entry f e == e' /\
      fmap_trace f tr2 == tr2'
    )
  = fmap_trace_prefix f tr (ts + 1);
    trace_subtract_fmap_trace (prefix tr (ts + 1)) tr f

let trace_split_matches_prefix (#label_t:Type) (tr:trace_ label_t) (ts:timestamp {ts `on_trace` tr})
  : Lemma
    (
      let (tr1, e, _) = trace_split tr ts in
      tr1 == prefix tr ts /\
      append_entry tr1 e == prefix tr (ts + 1)
    )
  = let (tr1, e, _) = trace_split tr ts in
    prefix_prefix_eq tr1 (prefix tr (ts + 1)) ts

let trace_split_grows (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts `on_trace` tr})
  : Lemma
    (
      let (tr1, e, _) = trace_split tr ts in
      tr1 <$ tr /\
      (append_entry tr1 e) <$ tr
    )
  = trace_split_matches_prefix tr ts

/// trace_split_at is a version of trace_split that allows us to more easily avoid
/// dealing explicitly with timestamps in proofs, as we do not need to first use the
/// fact that an entry exists on the trace to find the corresponding timestamp before
/// splitting at that entry.

let trace_split_at (#a:Type) (tr:trace_ a) (e:trace_entry_ a{entry_exists tr e})
  : (trace_ a & (e':trace_entry_ a{trace_entry_equiv e e'}) & trace_ a)
  = let idx = trace_find_first tr e in
    let (tr1, e', tr2) = trace_split tr idx in
    trace_split_get_entry tr idx idx;
    (tr1, e', tr2)


/// Properties relating split with concat and subtract

let trace_split_concat (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts `on_trace` tr})
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
       (append_entry tr1 e) <++> tr2 == tr
    )
  = trace_concat_subtract (prefix tr (ts + 1)) tr

let trace_subtract_matches_split (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2 /\ is_not_empty tr1)
    (ensures (
      let (_, _, tl) = trace_split tr2 (trace_length tr1 - 1) in
      tl == (tr2 <--> tr1)
    ))
  = prefix_prefix_eq tr1 tr2 (trace_length tr1)

