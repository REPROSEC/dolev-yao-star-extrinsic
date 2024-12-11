module DY.Core.Trace.Arithmetic

open DY.Core.Trace.Type
open DY.Core.Trace.Base

(*** Trace arithmetic ***)

/// We define trace concatenation (the monoid operation), as well as
/// trace subtraction, which is defined for traces tr2 <$ tr1, and yields the suffix of
/// tr1 beginning after tr2.

[@@"opaque_to_smt"]
val trace_concat: #label_t:Type -> trace_ label_t -> trace_ label_t -> trace_ label_t
let rec trace_concat tr1 tr2 =
  match tr2 with
  | Nil -> tr1
  | Snoc hd e -> append_entry (trace_concat tr1 hd) e

[@@"opaque_to_smt"]
val trace_subtract: #label_t:Type -> tr1:trace_ label_t -> tr2:trace_ label_t{tr2 <$ tr1} -> trace_ label_t
let rec trace_subtract tr1 tr2 =
  if trace_length tr1 = trace_length tr2 then empty_trace
  else begin
    let Snoc hd e = tr1 in
    grows_cases tr2 tr1;
    append_entry (trace_subtract hd tr2) e
  end

let (<++>) = trace_concat
let (<-->) = trace_subtract

/// Traces form a monoid with trace concatenation as operation, and empty_trace as unit.

val trace_concat_empty_trace: #label_t:Type -> tr:trace_ label_t ->
  Lemma
  (
    tr <++> empty_trace == tr /\
    empty_trace <++> tr == tr
  )
  [SMTPatOr [[SMTPat (tr <++> empty_trace)]; [SMTPat (empty_trace <++> tr)]]]
let rec trace_concat_empty_trace #label_t tr =
  reveal_opaque (`%trace_concat) (trace_concat #label_t);
  match tr with
  | Nil -> ()
  | Snoc hd _ -> trace_concat_empty_trace hd

val trace_concat_assoc:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t -> tr3:trace_ label_t ->
  Lemma (((tr1 <++> tr2) <++> tr3) == (tr1 <++> (tr2 <++> tr3)))
let rec trace_concat_assoc #label_t tr1 tr2 tr3 =
  reveal_opaque (`%trace_concat) (trace_concat #label_t);
  match tr3 with
  | Nil -> ()
  | Snoc hd _ -> trace_concat_assoc tr1 tr2 hd

/// Further properties of trace concatenation

val append_entry_is_concat_singleton: #label_t:Type -> tr:trace_ label_t -> e:trace_entry_ label_t ->
  Lemma (append_entry tr e == (tr <++> (append_entry empty_trace e)))
  [SMTPat (tr <++> (append_entry empty_trace e))]
let append_entry_is_concat_singleton #label_t tr e =
  reveal_opaque (`%trace_concat) (trace_concat #label_t)

val trace_concat_grows: #label_t:Type -> tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma (tr1 <$ (tr1 <++> tr2))
  [SMTPat (tr1 <$ (tr1 <++> tr2))]
let rec trace_concat_grows #label_t tr1 tr2 =
  reveal_opaque (`%trace_concat) (trace_concat #label_t);
  match tr2 with
  | Nil -> ()
  | Snoc hd e -> trace_concat_grows tr1 hd

val trace_concat_trace_length: #label_t:Type -> tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma (trace_length (tr1 <++> tr2) == trace_length tr1 + trace_length tr2)
  [SMTPat (trace_length (tr1 <++> tr2))]
let rec trace_concat_trace_length #label_t tr1 tr2 =
  reveal_opaque (`%trace_concat) (trace_concat #label_t);
  match tr2 with
  | Nil -> ()
  | Snoc hd e -> trace_concat_trace_length tr1 hd

val trace_concat_get_entry:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  ts:timestamp ->
  Lemma
  (requires ts `on_trace` (tr1 <++> tr2))
  (ensures (
    get_entry_at (tr1 <++> tr2) ts ==
    (if ts `on_trace` tr1
      then get_entry_at tr1 ts
      else get_entry_at tr2 (ts - trace_length tr1)
    )
  ))
let rec trace_concat_get_entry #label_t tr1 tr2 ts =
  reveal_opaque (`%trace_concat) (trace_concat #label_t);
  if is_empty tr2 || ts = last_timestamp (tr1 <++> tr2) then ()
  else trace_concat_get_entry tr1 (init tr2) ts

val trace_concat_fmap_trace:
  #a:Type -> #b:Type ->
  tr1:trace_ a -> tr2:trace_ a ->
  f:(a -> b) ->
  Lemma ((fmap_trace f (tr1 <++> tr2) == ((fmap_trace f tr1) <++> (fmap_trace f tr2))))
let rec trace_concat_fmap_trace #a #b tr1 tr2 f =
  reveal_opaque (`%trace_concat) (trace_concat #a);
  reveal_opaque (`%trace_concat) (trace_concat #b);
  match tr2 with
  | Nil -> ()
  | Snoc hd e -> trace_concat_fmap_trace tr1 hd f


/// Properties of trace subtraction

val trace_subtract_append_entry:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  e:trace_entry_ label_t ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures ((append_entry tr2 e) <--> tr1) == append_entry (tr2 <--> tr1) e)
  [SMTPat ((append_entry tr2 e) <--> tr1)]
let trace_subtract_append_entry #label_t tr1 tr2 e =
  reveal_opaque (`%trace_subtract) (trace_subtract #label_t)

val trace_subtract_trace_length:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures trace_length (tr2 <--> tr1) == trace_length tr2 - trace_length tr1)
  [SMTPat (trace_length (tr2 <--> tr1))]
let rec trace_subtract_trace_length #label_t tr1 tr2 =
  reveal_opaque (`%trace_subtract) (trace_subtract #label_t);
  if trace_length tr2 = trace_length tr1 then ()
  else begin
    grows_cases tr1 tr2;
    trace_subtract_trace_length tr1 (init tr2)
  end

val trace_subtract_get_entry:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  ts:timestamp ->
  Lemma
  (requires tr1 <$ tr2 /\ ts `on_trace` tr2)
  (ensures (
    get_entry_at tr2 ts == (
      if ts `on_trace` tr1
      then get_entry_at tr1 ts
      else get_entry_at (tr2 <--> tr1) (ts - trace_length tr1)
    )
  ))
let rec trace_subtract_get_entry #label_t tr1 tr2 ts =
  reveal_opaque (`%trace_subtract) (trace_subtract #label_t);
  grows_cases tr1 tr2;
  if ts `on_trace` tr1
  then get_entry_at_grows tr1 tr2 ts
  else if ts = last_timestamp tr2
  then ()
  else trace_subtract_get_entry tr1 (init tr2) ts

val trace_subtract_fmap_trace:
  #a:Type -> #b:Type ->
  tr1:trace_ a -> tr2:trace_ a ->
  f:(a ->b) ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures (fmap_trace f (tr2 <--> tr1) == ((fmap_trace f tr2) <--> (fmap_trace f tr1))))
let rec trace_subtract_fmap_trace #a #b tr1 tr2 f =
  reveal_opaque (`%trace_subtract) (trace_subtract #a);
  reveal_opaque (`%trace_subtract) (trace_subtract #b);
  grows_cases tr1 tr2;
  if trace_length tr2 = trace_length tr1 then ()
  else trace_subtract_fmap_trace tr1 (init tr2) f


/// Properties connecting trace concatenation and subtraction

val trace_concat_subtract: #label_t:Type -> tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma (tr2 == ((tr1 <++> tr2) <--> tr1))
  [SMTPat ((tr1 <++> tr2) <--> tr1)]
let rec trace_concat_subtract #label_t tr1 tr2 =
  reveal_opaque (`%trace_concat) (trace_concat #label_t);
  reveal_opaque (`%trace_subtract) (trace_subtract #label_t);
  match tr2 with
  | Nil -> ()
  | Snoc hd e -> trace_concat_subtract tr1 hd

val trace_subtract_concat:
  #label_t:Type ->
  tr1:trace_ label_t -> tr2:trace_ label_t ->
  Lemma
  (requires tr1 <$ tr2)
  (ensures tr1 <++> (tr2 <--> tr1) == tr2)
  [SMTPat (tr1 <++> (tr2 <--> tr1))]
let rec trace_subtract_concat #label_t tr1 tr2 =
  reveal_opaque (`%trace_concat) (trace_concat #label_t);
  reveal_opaque (`%trace_subtract) (trace_subtract #label_t);
  grows_cases tr1 tr2;
  eliminate tr2 == tr1 \/ (is_not_empty tr2 /\ tr1 <$ (init tr2))
  returns tr1 <++> (tr2 <--> tr1) == tr2
  with _. ()
  and _. trace_subtract_concat tr1 (init tr2)
