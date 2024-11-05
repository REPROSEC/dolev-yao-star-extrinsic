module DY.Core.Trace.SplitUtils

open DY.Core.Trace.Type
open DY.Core.Trace.Base

/// Overall TODO: Many of the functions here can (and should) be made opaque to SMT,
/// and then revealed in lemmas as necessary.

(*** Lemmas on prefixes ***)
/// TODO: These may belong in DY.Core.Trace.Base alongside the other prefix lemmas.

let nil_prefix (#label_t:Type) (tr:trace_ label_t)
  : Lemma (ensures Nil <$ tr)
    [SMTPat (Nil <$ tr)]
  = normalize_term_spec (grows #label_t)

let prefix_full_eq (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (requires tr1 <$ tr2 /\ length tr1 == length tr2)
    (ensures tr1 == tr2)
// TODO:
// It is not clear if this SMTPat is ever practically useful, but it seems like it could be in principle
    [SMTPat (tr1 == tr2); SMTPat (tr1 <$ tr2)]
  = normalize_term_spec (grows #label_t)


(*** General utility functions for working with traces ***)

// This function is not terribly important, but we often want to check if we are at
// the end of a trace, and hiding the off-by-one between length and the last index
// inside a function makes things look cleaner.
let last_ts (#label_t:Type) (tr:trace_ label_t{Snoc? tr}) : timestamp = length tr - 1

// Now that trace entries are abstracted over label types, we cannot compare
// trace entries for equality with =. This function implements trace equality
// when the label type is an eqtype (as for unit, for instance).
let trace_entry_equal (#label_t:eqtype) (e1 e2:trace_event_ label_t)
  : bool
  = match (e1, e2) with
    | MsgSent b1, MsgSent b2 -> b1 = b2
    | RandGen u1 l1 i1, RandGen u2 l2 i2 -> u1 = u2 && l1 = l2 && i1 = i2
    | Corrupt ts1, Corrupt ts2 -> ts1 = ts2
    | SetState p1 sid1 b1, SetState p2 sid2 b2 -> p1 = p2 && sid1 = sid2 && b1 = b2
    | Event p1 t1 b1, Event p2 t2 b2 -> p1 = p2 && t1 = t2 && b1 = b2
    | _ -> false

// By forgetting labels, we can work with a label-ignoring equivalence on entries
let trace_entry_equiv (#label_t:Type) (e1 e2:trace_event_ label_t)
  : bool
  = trace_entry_equal #unit (fmap_trace_event forget_label e1) (fmap_trace_event forget_label e2)

let trace_entry_equal_is_eq (#label_t:eqtype) (e1 e2:trace_event_ label_t)
  : Lemma
    (ensures trace_entry_equal e1 e2 <==> e1 == e2)
    [SMTPat (trace_entry_equal e1 e2)]
  = ()

// trace_entry_equiv is an equivalence relation
let trace_entry_equiv_reflexive (#label_t:Type) (e:trace_event_ label_t)
  : Lemma
    (ensures trace_entry_equiv e e)
    [SMTPat (trace_entry_equiv e e)]
  = ()

let trace_entry_equiv_symmetric (#label_t:Type) (e1 e2:trace_event_ label_t)
  : Lemma
    (requires trace_entry_equiv e1 e2)
    (ensures trace_entry_equiv e2 e1)
  = ()

let trace_entry_equiv_transitive (#label_t:Type) (e1 e2 e3:trace_event_ label_t)
  : Lemma
    (requires
       trace_entry_equiv e1 e2 /\
       trace_entry_equiv e2 e3
    )
    (ensures trace_entry_equiv e1 e3)
  = ()

(*** Trace search functions ***)

/// As trace entries are not an eqtype, rather than looking up a specific trace entry,
/// we first implement a function that lets us look up trace entries with a given property.
/// Currently, this will find the most recent entry satisfying the property, if multiple
/// exist, but it is easy to generalize to find the oldest such entry, or all such entries.
///
/// Using trace entry equivalence and this first search function, we can find entries that are
/// equivalent to a known trace entry, though they may not necessarily be equal.

let rec trace_findP (#label_t:Type) (tr:trace_ label_t) (p:trace_event_ label_t -> bool)
  : Pure (option timestamp)
    (requires True)
    (ensures fun ts_opt ->
       match ts_opt with
       | None -> forall ts. ts < length tr ==> ~(p(get_event_at tr ts))
       | Some ts -> ts < length tr /\ p (get_event_at tr ts)
    )
  = match tr with
    | Nil -> None
    | Snoc hd entry ->
      if p entry then
        Some (last_ts tr)
      else
        trace_findP hd p

let trace_find (#label_t:Type) (tr:trace_ label_t) (e:trace_event_ label_t{event_exists tr e})
  : Pure timestamp (requires True) (ensures fun ts -> ts < length tr /\ trace_entry_equiv e (get_event_at tr ts))
  = let Some ts = trace_findP tr (fun e' -> trace_entry_equiv e e') in
    ts


(*** Trace splitting functions ***)

/// In reasoning about the trace, we most often make use of the prefix function to extract
/// the portion of a trace before some entry that we are focused on. For some purposes, however,
/// for instance, to give a modifies analysis for a trace-passing function which specifies what
/// pieces of state it may modify, it is useful to look at suffixes as well (e.g., the suffix of
/// the output trace that is its "difference" with the input trace).
///
/// The trace splitting functions here unify getting prefixes and suffixes, either based on a
/// timestamp or a particular event.
///
/// The trace split function is also compatible with the various other trace functions ---
/// in particular, length and get_event_at, which give us a correctness guarantee of the split,
/// but also prefix, grows/<$, and fmap_trace.

let rec trace_split (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : (trace_ label_t & trace_event_ label_t & trace_ label_t)
  = let Snoc hd entry = tr in
    if ts = last_ts tr then
      (hd, entry, Nil)
    else
      let (tr1, e, tr2') = trace_split hd ts in
      (tr1, e, Snoc tr2' entry)

let rec trace_split_length (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : Lemma
    (requires True)
    (ensures (
      let (tr1, e, tr2) = trace_split tr ts in
      length tr1 = ts /\ length tr2 = (length tr) - ts - 1
    ))
//    TODO: This SMTPat doesn't seem to do much, but I'm not sure how to set up a better one
//    [SMTPatOr [
//      [SMTPat (length (Mktuple3?._1 (trace_split tr ts)))];
//      [SMTPat (length (Mktuple3?._3 (trace_split tr ts)))]
//    ]]
  = let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else trace_split_length hd ts

let rec trace_split_left (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr}) (i:timestamp{i < ts})
  : Lemma
    (requires True)
    (ensures (
      let (tr1, _, _) = trace_split tr ts in
      length tr1 = ts /\
      get_event_at tr1 i == get_event_at tr i
    ))
  = let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else trace_split_left hd ts i

let rec trace_split_mid (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : Lemma
    (requires True)
    (ensures (
      let (_, e, _) = trace_split tr ts in
      e == get_event_at tr ts
    ))
  = let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else trace_split_mid hd ts

let rec trace_split_right (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr}) (i:timestamp{ts < i /\ i < length tr})
  : Lemma
    (requires True)
    (ensures (
      let (_, _, tr2) = trace_split tr ts in
      length tr2 = (length tr) - ts - 1 /\
      get_event_at tr2 (i - ts - 1) == get_event_at tr i
    ))
  = let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else begin
      trace_split_length tr ts;
      if i < length hd then
        trace_split_right hd ts i
      else ()
    end

let rec trace_split_matches_prefix (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : Lemma
    (ensures (
      let (tr1, e, _) = trace_split tr ts in
      tr1 == prefix tr ts /\
      (Snoc tr1 e) == prefix tr (ts + 1)
    ))
  = let Snoc hd entry = tr in
    normalize_term_spec (prefix #label_t);
    if ts = last_ts tr then ()
    else trace_split_matches_prefix hd ts

let trace_split_grows (#label_t:Type) (tr:trace_ label_t) (ts:timestamp {ts < length tr})
  : Lemma
    (ensures (
      let (tr1, e, _) = trace_split tr ts in
      tr1 <$ tr /\
      (Snoc tr1 e) <$ tr
    ))
  = trace_split_matches_prefix tr ts

let rec trace_split_fmap (#a #b:Type) (tr:trace_ a) (ts:timestamp {ts < length tr}) (f:a -> b)
  : Lemma
    (ensures (
      let (tr1, e, tr2) = trace_split tr ts in
      let (tr1', e', tr2') = trace_split (fmap_trace f tr) ts in
      fmap_trace f tr1 == tr1' /\
      fmap_trace_event f e == e' /\
      fmap_trace f tr2 == tr2'
    ))
  = let Snoc hd entry = tr in
    if ts = last_ts tr then ()
    else trace_split_fmap hd ts f

let trace_split_at (#a:Type) (tr:trace_ a) (e:trace_event_ a{event_exists tr e})
  : (trace_ a & (e':trace_event_ a{trace_entry_equiv e e'}) & trace_ a)
  = let idx = trace_find tr e in
    let (tr1, e', tr2) = trace_split tr idx in
    trace_split_mid tr idx;
    (tr1, e', tr2)


(*** Trace arithmetic ***)

/// We define trace concatenation (the monoid operation), as well as
/// trace subtraction, which is defined for traces tr2 <$ tr1, and yields the suffix of
/// tr1 beginning after tr2.

let rec trace_concat (#label_t:Type) (tr1 tr2:trace_ label_t)
  : trace_ label_t
  = match tr2 with
    | Nil -> tr1
    | Snoc hd e -> Snoc (trace_concat tr1 hd) e

let trace_subtract (#label_t:Type) (tr1:trace_ label_t) (tr2:trace_ label_t{tr2 <$ tr1})
  : trace_ label_t
  = match tr2 with
    | Nil -> tr1
    | _ -> let (_, _, tl) = trace_split tr1 (length tr2 - 1) in
          tl

let (<++>) = trace_concat
let (<-->) = trace_subtract

/// Traces form a monoid with trace concatenation as operation, and Nil as unit.

let rec trace_concat_nil (#label_t:Type) (tr:trace_ label_t)
  : Lemma
    (ensures (
      tr <++> Nil == tr /\
      Nil <++> tr == tr
    ))
    [SMTPatOr [[SMTPat (tr <++> Nil)]; [SMTPat (Nil <++> tr)]]]
  = match tr with
    | Nil -> ()
    | Snoc hd _ -> trace_concat_nil hd

let rec trace_concat_assoc (#label_t:Type) (tr1 tr2 tr3:trace_ label_t)
  : Lemma
    (ensures ((tr1 <++> tr2) <++> tr3) == (tr1 <++> (tr2 <++> tr3)))
  = match tr3 with
    | Nil -> ()
    | Snoc hd _ -> trace_concat_assoc tr1 tr2 hd

let trace_subtract_nil (#label_t:Type) (tr:trace_ label_t)
  : Lemma
    (ensures (tr <--> Nil) == tr)
    [SMTPat (tr <--> Nil)]
  = ()


/// Properties connecting trace concatenation, splitting, and subtraction.

let rec trace_split_concat (#label_t:Type) (tr:trace_ label_t) (ts:timestamp{ts < length tr})
  : Lemma
    (ensures (
      let (tr1, e, tr2) = trace_split tr ts in
      (Snoc tr1 e) <++> tr2 == tr
    ))
  = let Snoc hd e = tr in
    if ts = last_ts tr then ()
    else trace_split_concat hd ts

let trace_subtract_concat (#label_t:Type) (tr1:trace_ label_t) (tr2:trace_ label_t{tr2 <$ tr1})
  : Lemma
    (ensures tr2 <++> (tr1 <--> tr2) == tr1)
  = match tr2 with
    | Nil -> ()
    | Snoc hd e ->
    begin
      trace_split_matches_prefix tr1 (length tr2 - 1);
      prefix_full_eq (prefix tr2 (length tr2)) tr2;
      trace_split_concat tr1 (length tr2 - 1);
      ()
    end
