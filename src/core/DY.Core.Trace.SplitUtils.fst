module DY.Core.Trace.SplitUtils

open DY.Core.Trace.Type
open DY.Core.Trace.Base

(*** General utility functions for working with traces ***)

/// This function is not terribly important, but we often want to check if we are at
/// the end of a trace, and hiding the off-by-one between length and the last index
/// inside a function makes things look cleaner.

let last_ts (#label_t:Type) (tr:trace_ label_t{Snoc? tr}) : timestamp = length tr - 1

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
       | None -> forall ts. ts < length tr ==> ~(p(get_entry_at tr ts))
       | Some ts -> ts < length tr /\ p (get_entry_at tr ts)
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
  : Pure timestamp (requires True) (ensures fun ts -> ts < length tr /\ trace_entry_equiv e (get_entry_at tr ts))
  = let Some ts = trace_search tr (trace_entry_equiv e) in
    ts


(*** Trace splitting functions ***)

/// In reasoning about the trace, we most often make use of the prefix function to extract
/// the portion of a trace before some entry that we are focused on. For some purposes, however,
/// for instance, to give a modifies analysis for a trace-passing function which specifies what
/// pieces of state it may modify, it is useful to look at suffixes as well (e.g., the suffix of
/// the output trace that is its "difference" with the input trace).
///
/// The trace splitting functions here unify getting prefixes and suffixes, either based on a
/// timestamp or a particular entry.
///
/// The trace split function is also compatible with the various other trace functions ---
/// in particular, length and get_entry_at, which give us a correctness guarantee of the split,
/// but also prefix, grows/<$, and fmap_trace.

[@@"opaque_to_smt"]
let rec trace_split (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : (trace_ label_t & trace_entry_ label_t & trace_ label_t)
  = let Snoc hd entry = tr in
    if ts = last_ts tr then
      (hd, entry, Nil)
    else
      let (tr1, e, tr2') = trace_split hd ts in
      (tr1, e, Snoc tr2' entry)

let rec trace_split_length (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
      length tr1 = ts /\ length tr2 = (length tr) - ts - 1
    )
    [SMTPat (trace_split tr ts)]
  = norm_spec [zeta; delta_only [`%trace_split]] (trace_split #label_t);
    let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else trace_split_length hd ts

let rec trace_split_get_entry (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr}) (i:timestamp{i < length tr})
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
      get_entry_at tr i == (
        if i < ts then get_entry_at tr1 i
        else if i = ts then e
        else get_entry_at tr2 (i - ts - 1)
      )
    )
  = norm_spec [zeta; delta_only [`%trace_split]] (trace_split #label_t);
    let Snoc hd entry = tr in
    if ts = last_ts tr || i >= length hd then ()
    else trace_split_get_entry hd ts i

let rec trace_split_matches_prefix (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : Lemma
    (
      let (tr1, e, _) = trace_split tr ts in
      tr1 == prefix tr ts /\
      (Snoc tr1 e) == prefix tr (ts + 1)
    )
  = norm_spec [zeta; delta_only [`%trace_split]] (trace_split #label_t);
    norm_spec [zeta; delta_only [`%prefix]] (prefix #label_t);
    let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else trace_split_matches_prefix hd ts

let rec trace_split_fmap (#a #b:Type) (tr:trace_ a) (ts:timestamp {ts < length tr}) (f:a -> b)
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
      let (tr1', e', tr2') = trace_split (fmap_trace f tr) ts in
      fmap_trace f tr1 == tr1' /\
      fmap_trace_entry f e == e' /\
      fmap_trace f tr2 == tr2'
    )
  = norm_spec [zeta; delta_only [`%trace_split]] (trace_split #a);
    norm_spec [zeta; delta_only [`%trace_split]] (trace_split #b);
    let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else trace_split_fmap hd ts f

(*** Trace arithmetic ***)

/// We define trace concatenation (the monoid operation), as well as
/// trace subtraction, which is defined for traces tr2 <$ tr1, and yields the suffix of
/// tr1 beginning after tr2.

[@@"opaque_to_smt"]
let rec trace_concat (#label_t:Type) (tr1 tr2:trace_ label_t)
  : trace_ label_t
  = match tr2 with
    | Nil -> tr1
    | Snoc hd e -> Snoc (trace_concat tr1 hd) e

[@@"opaque_to_smt"]
let rec trace_subtract (#label_t:Type) (tr1:trace_ label_t) (tr2:trace_ label_t{tr2 <$ tr1})
  : trace_ label_t
  = if length tr1 = length tr2 then Nil
    else begin
      let Snoc hd e = tr1 in
      grows_cases tr2 tr1;
      Snoc (trace_subtract hd tr2) e
    end

let (<++>) = trace_concat
let (<-->) = trace_subtract

/// Traces form a monoid with trace concatenation as operation, and Nil as unit.

let rec trace_concat_nil (#label_t:Type) (tr:trace_ label_t)
  : Lemma
    (
      tr <++> Nil == tr /\
      Nil <++> tr == tr
    )
    [SMTPatOr [[SMTPat (tr <++> Nil)]; [SMTPat (Nil <++> tr)]]]
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
    (Snoc tr e == (tr <++> (Snoc Nil e)))
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

let trace_subtract_snoc_left (#label_t:Type) (tr1 tr2:trace_ label_t) (e:trace_entry_ label_t)
  : Lemma
    (requires tr1 <$ tr2)
    (ensures ((Snoc tr2 e) <--> tr1) == Snoc (tr2 <--> tr1) e)
    [SMTPat ((Snoc tr2 e) <--> tr1)]
  = norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #label_t)

/// Properties connecting trace concatenation, splitting, and subtraction.

let rec trace_split_concat (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : Lemma
    (
      let (tr1, e, tr2) = trace_split tr ts in
      (Snoc tr1 e) <++> tr2 == tr
    )
  = norm_spec [zeta; delta_only [`%trace_concat]] (trace_concat #label_t);
    norm_spec [zeta; delta_only [`%trace_split]] (trace_split #label_t);
    let Snoc hd e = tr in
    if ts = last_ts tr then ()
    else trace_split_concat hd ts

let rec trace_subtract_matches_split (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2 /\ Snoc? tr1)
    (ensures (
      let (_, _, tl) = trace_split tr2 (length tr1 - 1) in
      tl == (tr2 <--> tr1)
    ))
  = norm_spec [zeta; delta_only [`%trace_subtract]] (trace_subtract #label_t);
    norm_spec [zeta; delta_only [`%trace_split]] (trace_split #label_t);
    let Snoc hd e = tr2 in
    let (_, _, tl) = trace_split tr2 (length tr1 - 1) in
    grows_cases tr1 tr2;
    eliminate tr1 == tr2 \/ tr1 <$ hd
    returns tl == (tr2 <--> tr1)
    with _. ()
    and _. trace_subtract_matches_split tr1 hd

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
    eliminate tr2 == tr1 \/ (Snoc? tr2 /\ (let Snoc hd _ = tr2 in tr1 <$ hd))
    returns tr1 <++> (tr2 <--> tr1) == tr2
    with _. ()
    and _. begin
      let Snoc hd e = tr2 in
      trace_subtract_concat tr1 hd
    end
