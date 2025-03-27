module DY.Lib.Event.Typed

open Comparse
open DY.Core
open DY.Lib.SplitFunction
open DY.Lib.Comparse.Glue

/// This module defines user-friendly API for protocol events.
/// It does it in three ways.
///
/// First, the API uses the split predicate methodology,
/// so that the global event predicate can be defined modularly
/// (see DY.Lib.SplitFunction).
///
/// Second, the API is integrated with Comparse,
/// so that the event content is a high-level type
/// instead of being a bare `bytes`.
///
/// Finally, the API rely on a typeclass
/// that associate an F* to an event tag and message format.
/// This removes some unnecessary boilerplate in the functions arguments.

(*** Event typeclass ***)

class event (a:Type0) = {
  tag: string;
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  format: parseable_serializeable bytes a;
}

val mk_event_instance:
  #a:Type0 -> {|parseable_serializeable bytes a|} -> string ->
  event a
let mk_event_instance #a #format tag = {
  tag;
  format;
}

(*** Split predicate ***)

type event_predicate (a:Type0) {|event a|} =
  trace -> principal -> a -> prop

let split_event_pred_params: split_function_parameters = {
  singleton_split_function_parameters string with

  tagged_data_t = trace & principal & string & bytes;
  raw_data_t = trace & principal & bytes;
  output_t = prop;

  decode_tagged_data = (fun (tr, prin, tag, content) -> (
    Some (tag, (tr, prin, content))
  ));

  local_fun_t = mk_dependent_type (trace -> principal -> bytes -> prop);
  global_fun_t = trace -> principal -> string -> bytes -> prop;

  default_global_fun = (fun tr prin tag content -> False);

  apply_local_fun = (fun epred (tr, prin, content) ->
    epred tr prin content
  );
  apply_global_fun = (fun epred (tr, prin, tag, content) ->
    epred tr prin tag content
  );
  mk_global_fun = (fun spred -> fun tr prin tag content ->
    spred (tr, prin, tag, content)
  );
  apply_mk_global_fun = (fun spred x -> ());
}

type compiled_event_predicate = trace -> principal -> bytes -> prop

val compile_event_pred:
  #a:Type0 -> {|event a|} ->
  event_predicate a ->
  compiled_event_predicate
let compile_event_pred #a #ev epred tr prin content_bytes =
  match parse a content_bytes with
  | None -> False
  | Some(content) -> epred tr prin content

val mk_event_tag_and_pred:
  #a:Type0 -> {|event a|} ->
  event_predicate a ->
  string & compiled_event_predicate
let mk_event_tag_and_pred #a #ev_a epred =
  (ev_a.tag, compile_event_pred epred)

[@@ "opaque_to_smt"]
val has_compiled_event_pred:
  {|protocol_invariants|} -> (string & compiled_event_predicate) -> prop
let has_compiled_event_pred #invs (tag, epred) =
  has_local_fun split_event_pred_params event_pred (|tag, epred|)

unfold
val has_event_pred:
  #a:Type0 -> {|event a|} ->
  {|protocol_invariants|} -> event_predicate a -> prop
let has_event_pred #a #ev #invs epred =
  has_compiled_event_pred (mk_event_tag_and_pred epred)

(*** Global event predicate builder ***)

val mk_event_pred:
  {|crypto_invariants|} -> list (string & compiled_event_predicate) ->
  trace -> principal -> string -> bytes -> prop
let mk_event_pred #cinvs tagged_local_preds =
  mk_global_fun split_event_pred_params (mk_dependent_tagged_local_funs tagged_local_preds)

val mk_event_pred_correct: {|protocol_invariants|} -> tagged_local_preds:list (string & compiled_event_predicate) -> Lemma
  (requires
    event_pred == mk_event_pred tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP has_compiled_event_pred tagged_local_preds)
let mk_event_pred_correct #invs tagged_local_preds =
  reveal_opaque (`%has_compiled_event_pred) (has_compiled_event_pred);
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst tagged_local_preds);
  for_allP_eq has_compiled_event_pred tagged_local_preds;
  map_dfst_mk_dependent_tagged_local_funs tagged_local_preds;
  FStar.Classical.forall_intro_2 (memP_mk_dependent_tagged_local_funs tagged_local_preds);
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_event_pred_params (mk_dependent_tagged_local_funs tagged_local_preds)))

(*** Monadic functions ***)

[@@ "opaque_to_smt"]
val trigger_event:
  #a:Type -> {|event a|} ->
  principal -> a ->
  traceful unit
let trigger_event #a #ev prin e =
  DY.Core.trigger_event prin ev.tag (serialize a e)

[@@ "opaque_to_smt"]
val event_triggered_at:
  #a:Type -> {|event a|} ->
  trace -> timestamp -> principal -> a ->
  prop
let event_triggered_at #a #ev tr i prin e =
  DY.Core.event_triggered_at tr i prin ev.tag (serialize a e)

val event_triggered:
  #a:Type -> {|event a|} ->
  trace -> principal -> a ->
  prop
let event_triggered #a #ev tr prin e =
  exists i. event_triggered_at tr i prin e

val trigger_event_event_triggered:
  #a:Type -> {|ev:event a|} ->
  prin:principal -> e:a -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = trigger_event prin e tr in
    event_triggered tr_out prin e
  ))
  [SMTPat (trigger_event #a #ev prin e tr);]
let trigger_event_event_triggered #a #ev prin e tr =
  reveal_opaque (`%trigger_event) (trigger_event #a);
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a)

val trigger_event_trace_invariant:
  {|protocol_invariants|} ->
  #a:Type -> {|ev:event a|} ->
  epred:event_predicate a ->
  prin:principal -> e:a -> tr:trace ->
  Lemma
  (requires
    epred tr prin e /\
    has_event_pred epred /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = trigger_event prin e tr in
    trace_invariant tr_out
  ))
  [SMTPat (trigger_event prin e tr);
   SMTPat (has_event_pred epred);
   SMTPat (trace_invariant tr)]
let trigger_event_trace_invariant #invs #a #ev epred prin e tr =
  reveal_opaque (`%has_compiled_event_pred) (has_compiled_event_pred);
  reveal_opaque (`%trigger_event) (trigger_event #a);
  local_eq_global_lemma split_event_pred_params event_pred ev.tag (compile_event_pred epred) (tr, prin, ev.tag, serialize _ e) ev.tag (tr, prin, serialize _ e)


val event_triggered_at_on_trace:
  #a:Type -> {|ev:event a|} ->
  tr:trace ->
  i:timestamp -> prin:principal -> e:a ->
  Lemma
  (requires
    event_triggered_at tr i prin e
  )
  (ensures i `on_trace` tr)
  [SMTPat (event_triggered_at #a #ev tr i prin e)]
let event_triggered_at_on_trace #a #ev  tr i prin e =
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a)

val event_triggered_at_implies_pred:
  {|protocol_invariants|} ->
  #a:Type -> {|ev:event a|} ->
  epred:event_predicate a -> tr:trace ->
  i:timestamp -> prin:principal -> e:a ->
  Lemma
  (requires
    event_triggered_at tr i prin e /\
    has_event_pred epred /\
    trace_invariant tr
  )
  (ensures epred (prefix tr i) prin e)
  [SMTPat (event_triggered_at tr i prin e);
   SMTPat (has_event_pred epred);
   SMTPat (trace_invariant tr);
  ]
let event_triggered_at_implies_pred #invs #a #ev epred tr i prin e =
  reveal_opaque (`%has_compiled_event_pred) (has_compiled_event_pred);
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  local_eq_global_lemma split_event_pred_params event_pred ev.tag (compile_event_pred epred) ((prefix tr i), prin, ev.tag, serialize _ e) ev.tag ((prefix tr i), prin, serialize _ e)

val event_triggered_grows:
  #a:Type -> {|ev:event a|} ->
  tr1:trace -> tr2:trace ->
  prin:principal -> e:a  ->
  Lemma
  (requires event_triggered tr1 prin e /\ tr1 <$ tr2)
  (ensures event_triggered tr2 prin e)
  [SMTPat (event_triggered tr1 prin e); SMTPat (tr1 <$ tr2)]
let event_triggered_grows #a #ev tr1 tr2 prin e =
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  ()

val event_triggered_at_implies_trace_entry_at:
  #a:Type -> {|ev:event a|} ->
  tr:trace -> i:timestamp -> prin:principal -> e:a  ->
  Lemma
  (requires event_triggered_at tr i prin e)
  (ensures
    get_entry_at tr i == Event prin ev.tag (serialize a e) /\
    parse #bytes a (serialize a e) == Some e
  )
  [SMTPat (event_triggered_at tr i prin e)]
let event_triggered_at_implies_trace_entry_at #a #ev tr i prin e =
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  ()

[@@ "opaque_to_smt"]
val find_event_triggered_at_timestamp:
  #a:Type -> {|event a|} ->
  tr:trace ->
  prin:principal -> content:a ->
  Pure timestamp
  (requires event_triggered tr prin content)
  (ensures fun i ->
    event_triggered_at tr i prin content /\
    ~(event_triggered (prefix tr i) prin content)
  )
let find_event_triggered_at_timestamp #a #ev_a tr prin content =
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  DY.Core.find_event_triggered_at_timestamp tr prin ev_a.tag (serialize a content)

val find_event_triggered_at_timestamp_later:
  #a:Type -> {|event a|} ->
  tr1:trace -> tr2:trace ->
  prin:principal -> content:a ->
  Lemma
  (requires
    event_triggered tr1 prin content /\
    tr1 <$ tr2
  )
  (ensures find_event_triggered_at_timestamp tr1 prin content == find_event_triggered_at_timestamp tr2 prin content)
  [SMTPat (find_event_triggered_at_timestamp tr1 prin content);
   SMTPat (find_event_triggered_at_timestamp tr2 prin content);
   SMTPat (tr1 <$ tr2)
  ]
let find_event_triggered_at_timestamp_later #a #ev_a tr1 tr2 prin content =
  reveal_opaque (`%find_event_triggered_at_timestamp) (find_event_triggered_at_timestamp #a);
  DY.Core.find_event_triggered_at_timestamp_later tr1 tr2 prin ev_a.tag (serialize a content)
