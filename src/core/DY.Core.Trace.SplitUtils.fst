module DY.Core.Trace.SplitUtils

open DY.Core.Trace.Type
open DY.Core.Trace.Base

(*** General utility functions for working with traces ***)

/// This function is not terribly important, but we often want to check if we are at
/// the end of a trace, and hiding the off-by-one between trace_length and the last index
/// inside a function makes things look cleaner.

let last_ts (#label_t:Type) (tr:trace_ label_t{is_not_empty tr}) : timestamp = trace_length tr - 1

/// By forgetting labels, we can work with a label-ignoring equivalence on entries

let trace_entry_equiv (#label_t:Type) (e1 e2:trace_entry_ label_t)
  : bool
  = (fmap_trace_entry forget_label e1) = (fmap_trace_entry forget_label e2)

(*** Trace search functions ***)

/// As trace entries are not an eqtype, rather than looking up a specific trace entry,
/// we first implement a function that lets us look up trace entries with a given property.
/// Currently, this will find the most recent entry satisfying the property, if multiple
/// exist, but it is easy to generalize to find the oldest such entry, or all such entries.
///
/// Using trace entry equivalence and this first search function, we can find entries that are
/// equivalent to a known trace entry, though they may not necessarily be equal.

[@@"opaque_to_smt"]
let rec trace_search (#label_t:Type) (tr:trace_ label_t) (p:trace_entry_ label_t -> bool)
  : Pure (option timestamp)
    (requires True)
    (ensures fun ts_opt ->
       match ts_opt with
       | None -> forall ts. ts `on_trace` tr ==> ~(p(get_entry_at tr ts))
       | Some ts -> ts `on_trace` tr /\ p (get_entry_at tr ts)
    )
  = match tr with
    | Nil -> None
    | Snoc hd entry ->
      if p entry then
        Some (last_ts tr)
      else
        trace_search hd p

[@@"opaque_to_smt"]
let trace_find (#label_t:Type) (tr:trace_ label_t) (e:trace_entry_ label_t{entry_exists tr e})
  : Pure timestamp (requires True) (ensures fun ts -> ts `on_trace` tr /\ trace_entry_equiv e (get_entry_at tr ts))
  = let Some ts = trace_search tr (trace_entry_equiv e) in
    ts

(*** Trace arithmetic ***)

/// We define trace concatenation (the monoid operation), as well as
/// trace subtraction, which is defined for traces tr2 <$ tr1, and yields the suffix of
/// tr1 beginning after tr2.

[@@"opaque_to_smt"]
let rec trace_concat (#label_t:Type) (tr1 tr2:trace_ label_t)
  : trace_ label_t
  = match tr2 with
    | Nil -> tr1
    | Snoc hd e -> append_entry (trace_concat tr1 hd) e

[@@"opaque_to_smt"]
let rec trace_subtract (#label_t:Type) (tr1:trace_ label_t) (tr2:trace_ label_t{tr2 <$ tr1})
  : trace_ label_t
  = if trace_length tr1 = trace_length tr2 then Nil
    else begin
      let Snoc hd e = tr1 in
      grows_cases tr2 tr1;
      append_entry (trace_subtract hd tr2) e
    end

let (<++>) = trace_concat
let (<-->) = trace_subtract

/// Traces form a monoid with trace concatenation as operation, and Nil as unit.

let rec trace_concat_nil (#label_t:Type) (tr:trace_ label_t)
  : Lemma
    (
      tr <++> empty_trace == tr /\
      empty_trace <++> tr == tr
    )
    [SMTPatOr [[SMTPat (tr <++> empty_trace)]; [SMTPat (empty_trace <++> tr)]]]
  = norm_spec [zeta; delta_only [`%trace_concat]] (trace_concat #label_t);
    match tr with
    | Nil -> ()
    | Snoc hd _ -> trace_concat_nil hd

let rec trace_concat_assoc (#label_t:Type) (tr1 tr2 tr3:trace_ label_t)
  : Lemma
    (((tr1 <++> tr2) <++> tr3) == (tr1 <++> (tr2 <++> tr3)))
  = norm_spec [zeta; delta_only [`%trace_concat]] (trace_concat #label_t);
    match tr3 with
    | Nil -> ()
    | Snoc hd _ -> trace_concat_assoc tr1 tr2 hd

let snoc_is_concat_singleton (#label_t:Type) (tr :trace_ label_t) (e:trace_entry_ label_t)
  : Lemma
    (append_entry tr e == (tr <++> (Snoc Nil e)))
    [SMTPat (tr <++> (Snoc Nil e))]
  = norm_spec [zeta; delta_only [`%trace_concat]] (trace_concat #label_t)

let rec trace_concat_grows (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (tr1 <$ (tr1 <++> tr2))
    [SMTPat (tr1 <$ (tr1 <++> tr2))]
  = norm_spec [zeta; delta_only [`%trace_concat]] (trace_concat #label_t);
    match tr2 with
    | Nil -> ()
    | Snoc hd e -> trace_concat_grows tr1 hd

/// Properties of trace subtraction

let trace_subtract_append_entry (#label_t:Type) (tr1 tr2:trace_ label_t) (e:trace_entry_ label_t)
  : Lemma
    (requires tr1 <$ tr2)
    (ensures ((append_entry tr2 e) <--> tr1) == append_entry (tr2 <--> tr1) e)
    [SMTPat ((append_entry tr2 e) <--> tr1)]
  = norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #label_t)

let rec trace_subtract_trace_length (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2)
    (ensures trace_length (tr2 <--> tr1) == trace_length tr2 - trace_length tr1)
    [SMTPat (trace_length (tr2 <--> tr1))]
  = norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #label_t);
    if trace_length tr2 = trace_length tr1 then ()
    else begin
      grows_cases tr1 tr2;
      trace_subtract_trace_length tr1 (init tr2)
    end

let rec trace_subtract_get_entry (#label_t:Type) (tr1 tr2:trace_ label_t) (i:timestamp{i `on_trace` tr2})
  : Lemma
    (requires tr1 <$ tr2 /\ i >= trace_length tr1)
    (ensures get_entry_at tr2 i == get_entry_at (tr2 <--> tr1) (i - trace_length tr1))
  = norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #label_t);
    if i = last_ts tr2 then ()
    else begin
      grows_cases tr1 tr2;
      trace_subtract_get_entry tr1 (init tr2) i
    end

let rec trace_subtract_fmap_trace (#a #b:Type) (tr1 tr2:trace_ a) (f:a -> b)
  : Lemma
    (requires tr1 <$ tr2)
    (ensures (fmap_trace f (tr2 <--> tr1) == ((fmap_trace f tr2) <--> (fmap_trace f tr1))))
  = norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #a);
    norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #b);
    if trace_length tr2 = trace_length tr1 then ()
    else begin
      grows_cases tr1 tr2;
      trace_subtract_fmap_trace tr1 (init tr2) f
    end


/// Properties connecting trace concatenation and subtraction

let rec trace_concat_subtract (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (tr2 == ((tr1 <++> tr2) <--> tr1))
    [SMTPat ((tr1 <++> tr2) <--> tr1)]
  = norm_spec [zeta; delta_only [`%trace_concat]] (trace_concat #label_t);
    norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #label_t);
    match tr2 with
    | Nil -> ()
    | Snoc hd e -> trace_concat_subtract tr1 hd

let rec trace_subtract_concat (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2)
    (ensures tr1 <++> (tr2 <--> tr1) == tr2)
    [SMTPat (tr1 <++> (tr2 <--> tr1))]
  = norm_spec [zeta; delta_only [`%trace_concat]] (trace_concat #label_t);
    norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #label_t);
    grows_cases tr1 tr2;
    eliminate tr2 == tr1 \/ (is_not_empty tr2 /\ tr1 <$ (init tr2))
    returns tr1 <++> (tr2 <--> tr1) == tr2
    with _. ()
    and _. trace_subtract_concat tr1 (init tr2)
