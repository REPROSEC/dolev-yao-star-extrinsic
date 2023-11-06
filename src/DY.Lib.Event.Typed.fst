module DY.Lib.Event.Typed

open Comparse
open DY.Core
open DY.Lib.SplitPredicate
open DY.Lib.Comparse.Glue

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

let split_event_pred_func: split_predicate_input_values = {
  labeled_data_t = trace & principal & string & bytes;
  label_t = string;
  encoded_label_t = string;
  raw_data_t = trace & principal & bytes;

  decode_labeled_data = (fun (tr, prin, tag, content) -> (
    Some (tag, (tr, prin, content))
  ));

  encode_label = (fun s -> s);
  encode_label_inj = (fun l1 l2 -> ());

  local_pred = trace -> principal -> bytes -> prop;
  global_pred = trace -> principal -> string -> bytes -> prop;

  apply_local_pred = (fun epred (tr, prin, content) ->
    epred tr prin content
  );
  apply_global_pred = (fun epred (tr, prin, tag, content) ->
    epred tr prin tag content
  );
  mk_global_pred = (fun spred -> fun tr prin tag content ->
    spred (tr, prin, tag, content)
  );
  apply_mk_global_pred = (fun spred x -> ());
}

type compiled_event_predicate = split_event_pred_func.local_pred

val compile_event_pred:
  #a:Type0 -> {|event a|} ->
  event_predicate a ->
  compiled_event_predicate
let compile_event_pred #a #ev epred tr prin content_bytes =
  match parse a content_bytes with
  | None -> False
  | Some(content) -> epred tr prin content

val has_compiled_event_pred:
  protocol_invariants -> (string & compiled_event_predicate) -> prop
let has_compiled_event_pred invs (label, epred) =
  has_local_pred split_event_pred_func event_pred (label, epred)

val has_event_pred:
  #a:Type0 -> {|event a|} ->
  protocol_invariants -> event_predicate a -> prop
let has_event_pred #a #ev invs epred =
  has_compiled_event_pred invs (ev.tag, compile_event_pred epred)

(*** Global event predicate builder ***)

val mk_event_pred: {|crypto_invariants|} -> list (string & compiled_event_predicate) -> trace -> principal -> string -> bytes -> prop
let mk_event_pred #cinvs l =
  mk_global_pred split_event_pred_func l

val mk_event_pred_correct: invs:protocol_invariants -> lpreds:list (string & compiled_event_predicate) -> Lemma
  (requires
    invs.trace_invs.event_pred == mk_event_pred lpreds /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds)
  )
  (ensures for_allP (has_compiled_event_pred invs) lpreds)
let mk_event_pred_correct invs lpreds =
  for_allP_eq (has_compiled_event_pred invs) lpreds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_pred_correct split_event_pred_func lpreds))

(*** Monadic functions ***)

[@@ "opaque_to_smt"]
val trigger_event:
  #a:Type -> {|event a|} ->
  principal -> a ->
  crypto unit
let trigger_event #a #ev prin e =
  DY.Core.trigger_event prin ev.tag (serialize a e)

[@@ "opaque_to_smt"]
val event_triggered_at:
  #a:Type -> {|event a|} ->
  trace -> nat -> principal -> a ->
  prop
let event_triggered_at #a #ev tr i prin e =
  DY.Core.event_triggered_at tr i prin ev.tag (serialize a e)

val event_triggered:
  #a:Type -> {|event a|} ->
  trace -> principal -> a ->
  prop
let event_triggered #a #ev tr prin e =
  exists i. event_triggered_at tr i prin e

val trigger_event_trace_invariant:
  {|invs:protocol_invariants|} ->
  #a:Type -> {|ev:event a|} ->
  epred:event_predicate a ->
  prin:principal -> e:a -> tr:trace ->
  Lemma
  (requires
    epred tr prin e /\
    has_event_pred invs epred /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = trigger_event prin e tr in
    trace_invariant tr_out /\
    event_triggered tr_out prin e
  ))
  [SMTPat (trigger_event prin e tr);
   SMTPat (has_event_pred invs epred);
   SMTPat (trace_invariant tr)]
let trigger_event_trace_invariant #invs #a #ev epred prin e tr =
  reveal_opaque (`%trigger_event) (trigger_event #a);
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  local_eq_global_lemma split_event_pred_func event_pred ev.tag (compile_event_pred epred) (tr, prin, ev.tag, serialize _ e) (tr, prin, serialize _ e)

val event_triggered_at_implies_pred:
  {|invs:protocol_invariants|} ->
  #a:Type -> {|ev:event a|} ->
  epred:event_predicate a -> tr:trace ->
  i:nat -> prin:principal -> e:a ->
  Lemma
  (requires
    event_triggered_at tr i prin e /\
    has_event_pred invs epred /\
    trace_invariant tr
  )
  (ensures i <= DY.Core.Trace.Type.length tr /\ epred (prefix tr i) prin e)
  [SMTPat (event_triggered_at tr i prin e);
   SMTPat (has_event_pred invs epred);
   SMTPat (trace_invariant tr);
  ]
let event_triggered_at_implies_pred #invs #a #ev epred tr i prin e =
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  local_eq_global_lemma split_event_pred_func event_pred ev.tag (compile_event_pred epred) ((prefix tr i), prin, ev.tag, serialize _ e) ((prefix tr i), prin, serialize _ e)

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

val event_triggered_at_implies_trace_event_at:
  #a:Type -> {|ev:event a|} ->
  tr:trace -> i:nat -> prin:principal -> e:a  ->
  Lemma
  (requires event_triggered_at tr i prin e)
  (ensures
    i < DY.Core.Trace.Type.length tr /\
    get_event_at tr i == Event prin ev.tag (serialize a e) /\
    parse #bytes a (serialize a e) == Some e
  )
  [SMTPat (event_triggered_at tr i prin e)]
let event_triggered_at_implies_trace_event_at #a #ev tr i prin e =
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  ()
