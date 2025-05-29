module DY.Lib.Label.Event

open Comparse
open DY.Core
open DY.Lib.Event.Typed

#set-options "--fuel 0 --ifuel 0"

/// `event_triggered_label` is corrupt when an event has been triggered.
/// This is useful for example in combination with `guard`.

[@@"opaque_to_smt"]
val bare_event_triggered_label:
  principal -> string -> bytes ->
  label
let bare_event_triggered_label prin tag content = mk_label {
  is_corrupt = (fun tr ->
    DY.Core.event_triggered tr prin tag content
  );
  is_corrupt_later = (fun tr1 tr2 -> ());
}

#push-options "--fuel 0 --ifuel 1"
val is_corrupt_bare_event_triggered_label:
  tr:trace ->
  prin:principal -> tag:string -> content:bytes ->
  Lemma (
    is_corrupt tr (bare_event_triggered_label prin tag content)
    <==>
    DY.Core.event_triggered tr prin tag content
  )
let is_corrupt_bare_event_triggered_label tr prin tag content =
  reveal_opaque (`%bare_event_triggered_label) (bare_event_triggered_label);
  reveal_opaque (`%is_corrupt) (is_corrupt);
  FStar.Classical.forall_intro (get_entry_at_fmap_trace forget_label tr);
  assert(DY.Core.event_triggered tr prin tag content <==> DY.Core.event_triggered (trace_forget_labels tr) prin tag content)
#pop-options

[@@"opaque_to_smt"]
val event_triggered_label:
  #a:Type0 -> {|event a|} ->
  principal -> a ->
  label
let event_triggered_label #a #ev_a prin content =
  bare_event_triggered_label prin ev_a.tag (serialize a content)

val is_corrupt_event_triggered_label:
  #a:Type0 -> {|event a|} ->
  tr:trace ->
  prin:principal -> content:a ->
  Lemma (
    is_corrupt tr (event_triggered_label prin content)
    <==>
    event_triggered tr prin content
  )
  [SMTPat (is_corrupt tr (event_triggered_label prin content))]
let is_corrupt_event_triggered_label #a #ev_a tr prin content =
  reveal_opaque (`%event_triggered_label) (event_triggered_label #a);
  reveal_opaque (`%event_triggered_at) (event_triggered_at #a);
  is_corrupt_bare_event_triggered_label tr prin ev_a.tag (serialize a content)


(*** Event labels for where the triggerer of the event is not important. ***)



// Labels where the 'triggerer' of the event is not important
val bare_event_triggered_by_anyone_label:
  string -> bytes ->
  label
let bare_event_triggered_by_anyone_label tag content = mk_label {
  is_corrupt = (fun tr ->
    exists prin. DY.Core.event_triggered tr prin tag content
  );
  is_corrupt_later = (fun tr1 tr2 -> ());
}

#push-options "--fuel 0 --ifuel 1"
val is_corrupt_bare_event_triggered_by_anyone_label:
  tr:trace ->
  tag:string -> content:bytes ->
  Lemma (
    is_corrupt tr (bare_event_triggered_by_anyone_label tag content)
    <==>
    exists prin. DY.Core.event_triggered tr prin tag content
  )
let is_corrupt_bare_event_triggered_by_anyone_label tr tag content =
  reveal_opaque (`%is_corrupt) (is_corrupt);
  FStar.Classical.forall_intro (get_entry_at_fmap_trace forget_label tr);
  assert(forall prin. DY.Core.event_triggered tr prin tag content <==> DY.Core.event_triggered (trace_forget_labels tr) prin tag content)
#pop-options

val event_triggered_by_anyone_label:
  #a:Type0 -> {|event a|} ->
  a ->
  label
let event_triggered_by_anyone_label #a #ev_a content =
  bare_event_triggered_by_anyone_label ev_a.tag (serialize a content)

val is_corrupt_event_triggered_by_anyone_label:
  #a:Type0 -> {|event a|} ->
  tr:trace ->
  content:a ->
  Lemma (
    is_corrupt tr (event_triggered_by_anyone_label content)
    <==>
    exists prin. event_triggered tr prin content
  )
  // [SMTPat (is_corrupt tr (event_triggered_by_anyone_label content))]
let is_corrupt_event_triggered_by_anyone_label #a #ev_a tr content =
  reveal_opaque (`%event_triggered_at) [event_triggered_at #a];
  is_corrupt_bare_event_triggered_by_anyone_label tr ev_a.tag (serialize a content)
