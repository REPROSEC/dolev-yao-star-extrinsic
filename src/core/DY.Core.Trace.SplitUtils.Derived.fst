module DY.Core.Trace.SplitUtils.Derived

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.SplitUtils

/// This module contains derived functions and lemmas based on
/// trace_split, trace_concat, trace_subtract, and their properties.

/// Derived functions for trace split

let trace_split_grows (#label_t:Type) (tr:trace_ label_t) (ts:timestamp {ts `on_trace` tr})
  : Lemma
    (ensures (
      let (tr1, e, _) = trace_split tr ts in
      tr1 <$ tr /\
      (append_entry tr1 e) <$ tr
    ))
  = trace_split_matches_prefix tr ts


let trace_split_at (#a:Type) (tr:trace_ a) (e:trace_entry_ a{entry_exists tr e})
  : (trace_ a & (e':trace_entry_ a{trace_entry_equiv e e'}) & trace_ a)
  = let idx = trace_find tr e in
    let (tr1, e', tr2) = trace_split tr idx in
    trace_split_get_entry tr idx idx;
    (tr1, e', tr2)

/// Derived functions for trace arithmetic

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
