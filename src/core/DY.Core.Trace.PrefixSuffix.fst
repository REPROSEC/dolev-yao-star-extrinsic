module DY.Core.Trace.PrefixSuffix

open DY.Core.List
open  DY.Core.Trace.Type
module Trace = DY.Core.Trace.Type
open DY.Core.Bytes.Type
open DY.Core.Label.Type

(*** Helper Lemmas for dealing with prefixes and suffixes of traces ***)

let rec prefix_including_event (tr:trace) (the_ev:trace_event{event_exists tr the_ev}) =
  match tr with
  | Snoc init ev ->
      if ev = the_ev 
        then tr
        else init `prefix_including_event` the_ev

let rec prefix_including_event_is_prefix (tr:trace) (the_ev:trace_event{event_exists tr the_ev}) :
  Lemma (tr `prefix_including_event` the_ev <$ tr)
  [SMTPat (tr `prefix_including_event` the_ev)] =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr with
  | Nil -> ()
  | Snoc init ev ->
         if ev = the_ev
           then ()
           else
             prefix_including_event_is_prefix init the_ev


/// definition of "trace substraction"
/// (it holds: tr2 = tr1 ++ tr2 `suffix_after` tr1)

val suffix_after: tr2:trace -> tr1:trace{tr1 <$ tr2} -> trace
let rec suffix_after tr2 tr1 = 
  match tr2 with
  | Nil -> Nil
  | Snoc init ev -> 
      if length tr2 = length tr1
        then Nil
        else begin 
             reveal_opaque (`%grows) grows; 
             norm_spec [zeta; delta_only [`%prefix]] (prefix);
             Snoc (suffix_after init tr1) ev
         end

val suffix_after_splits_trace:
  tr2:trace -> tr1:trace{tr1 <$ tr2} ->
  Lemma (tr2 = tr1 `trace_concat` (tr2 `suffix_after` tr1))
let rec suffix_after_splits_trace tr2 tr1 =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr2 with
  | Nil -> ()
  | Snoc init ev -> 
         if length tr1 = length tr2 
           then ()
           else suffix_after_splits_trace init tr1



/// for traces with tr1 <$ tr2 <$ tr3,
/// the suffix after tr1 on tr2
/// is a prefix of
/// the suffix after tr1 on tr3

val suffix_after_for_prefix: 
  tr3:trace -> tr2:trace {tr2 <$ tr3} -> tr1:trace {tr1 <$ tr2} ->
  Lemma 
    (tr2 `suffix_after` tr1 <$ tr3 `suffix_after` tr1)
let rec suffix_after_for_prefix tr3 tr2 tr1 = 
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  if length tr3 = length tr2 || length tr2 = length tr1
    then ()
    else begin
      match tr3 with
      | Nil -> ()
      | Snoc init ev -> suffix_after_for_prefix init tr2 tr1
    end


  
/// for traces with tr1 <$ tr2 <$ tr3,
/// the suffix after tr1 on tr3
/// is the concat of the two pairwise suffixes
#push-options "--fuel 2"
val suffix_after_concat:
  tr1:trace -> tr2:trace {tr1 <$ tr2} -> tr3:trace{tr2 <$ tr3} ->
  Lemma
  ( tr3 `suffix_after` tr1 == (tr2 `suffix_after` tr1) `trace_concat` (tr3 `suffix_after` tr2)
  )
let rec suffix_after_concat tr1 tr2 tr3 =     
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr3 with
  | Nil -> ()
  | Snoc init ev -> 
      if length tr2 = length tr3
        then ()
        else suffix_after_concat tr1 tr2 init
#pop-options

let suffix_after_event (tr:trace) (ev:trace_event{event_exists tr ev}) =
  let tr_before = tr `prefix_including_event` ev in
  tr `suffix_after` tr_before


let rec suffix_after_event_init
  (tr:trace{Snoc? tr}) (the_ev:trace_event{event_exists tr the_ev})
  :Lemma 
    ( let Snoc init ev = tr in
      if the_ev <> ev
        then tr `suffix_after_event` the_ev = Snoc (init `suffix_after_event` the_ev) ev
        else True
    )
= let Snoc init ev = tr in
  if the_ev <> ev
    then
      suffix_after_event_init init the_ev
    else ()


let rec has_suffix (tr:trace) (suff:trace) =
  match suff with
  | Nil -> true
  | Snoc suff_init suff_ev ->
      match tr with
      | Nil -> false
      | Snoc tr_init tr_ev ->
          suff_ev = tr_ev && (has_suffix tr_init suff_init)

let _ = 
  let ev1 = Corrupt "p" {the_id = 1} in 
  let ev2 = Corrupt "p" {the_id = 2} in 
  let ev3 = Corrupt "p" {the_id = 3} in 
  let tr = Snoc (Snoc (Snoc Nil ev1) ev2) ev3 in
  let tr' = Snoc (Snoc Nil ev2) ev3 in
  assert(tr `has_suffix` tr')


let rec suffix_after_is_suffix (tr:trace) (pref:trace{pref <$ tr}):
  Lemma
  (tr `has_suffix` (tr `suffix_after` pref)
  )
  [SMTPat (tr `has_suffix` (tr `suffix_after` pref))]
  =
  let suff = tr `suffix_after` pref in
  match suff with
  | Nil -> ()
  | Snoc suff_init suff_ev ->
         match tr with
         | Nil -> ()
         | Snoc tr_init tr_ev -> 
                assert(suff_ev = tr_ev);
                init_is_prefix tr;
                reveal_opaque (`%grows) grows; 
                suffix_after_is_suffix (tr_init) pref



let rec suffixes_ (tr:trace) (suff1:trace) (suff2:trace):
  Lemma
  (requires
      tr `has_suffix` suff1
    /\ tr `has_suffix` suff2
    /\ Trace.length suff1 >= Trace.length suff2
  )
  (ensures
        suff1 `has_suffix` suff2 
  )
  = match suff2 with
  | Nil -> ()
  | Snoc init2 last2 -> 
      let Snoc init1 last1 = suff1 in
      let Snoc init last = tr in 
      suffixes_ init init1 init2

let suffixes (tr:trace) (suff1:trace) (suff2:trace):
  Lemma
  (requires
      tr `has_suffix` suff1
    /\ tr `has_suffix` suff2
  )
  (ensures
        suff1 `has_suffix` suff2 
      \/ suff2 `has_suffix` suff1
  )
  = if Trace.length suff1 >= Trace.length suff2
       then suffixes_ tr suff1 suff2
       else suffixes_ tr suff2 suff1


let rec suffix_after_nil (tr:trace):
  Lemma (tr `suffix_after` Nil = tr)
  [SMTPat (tr `suffix_after` Nil)]
  = match tr with
    | Nil -> ()
    | Snoc init ev -> suffix_after_nil init


let prepend  (ev:trace_event) (tr:trace) =
  (Snoc Nil ev) `trace_concat` tr



let rec event_splits_trace (tr:trace) (ev:trace_event{event_exists tr ev}):
  Lemma
  ( let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    tr = tr_before `trace_concat` (prepend ev tr_after)
  )
  = let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    match tr with
    | Nil -> ()
    | Snoc tr_init tr_last ->
        if tr_last = ev
          then ()
          else event_splits_trace tr_init ev
        

let suffix_after_snoc (init:trace) (ev:trace_event) (pref:trace{pref <$ init}):
  Lemma
  ( reveal_opaque (`%grows) grows; 
    norm_spec [zeta; delta_only [`%prefix]] (prefix);

    (Snoc init ev) `suffix_after` pref = Snoc ( init `suffix_after` pref ) ev
  )
= normalize_term_spec suffix_after

let rec suffix_after_concat_ (pref:trace) (suff:trace):
  Lemma 
  ( let tr = pref `trace_concat` suff in
    trace_concat_grows pref suff;
    tr `suffix_after` pref = suff
  )
  = 
  let tr = pref `trace_concat` suff in
  match suff with
  | Nil -> ()
  | Snoc suff_init suff_ev ->
         suffix_after_concat_ pref suff_init;
         trace_concat_grows pref suff_init;
         suffix_after_snoc ( pref `trace_concat` suff_init  ) suff_ev pref

let suff_after_before_event_is_suff_at_event (tr:trace) (ev:trace_event{event_exists tr ev}):
  Lemma
  ( let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    tr `suffix_after` tr_before = (Snoc Nil ev) `trace_concat` tr_after
  )
  = let tr_before = tr `prefix_before_event` ev in
    let tr_after = tr `suffix_after_event` ev in
    event_splits_trace tr ev;
    suffix_after_concat_ tr_before (prepend ev tr_after)
    
