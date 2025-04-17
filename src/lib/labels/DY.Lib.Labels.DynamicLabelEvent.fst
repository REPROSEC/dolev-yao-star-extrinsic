module DY.Lib.Labels.DynamicLabelEvent

open Comparse
open DY.Core
open DY.Lib.Event.Typed
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

[@@ with_bytes bytes]
type reveal_event_format = {
  [@@@ with_parser #bytes ps_string]
  to:string;
  [@@@ with_parser #bytes ps_nat]
  point:nat;
}

%splice [ps_reveal_event_format] (gen_parser (`reveal_event_format))
%splice [ps_reveal_event_format_is_well_formed] (gen_is_well_formed_lemma (`reveal_event_format))

instance parseable_serializeable_bytes_reveal_event_format: parseable_serializeable bytes reveal_event_format =
  mk_parseable_serializeable ps_reveal_event_format

instance reveal_event : event reveal_event_format = mk_event_instance "Reveal"

let reveal_event_predicate = event_predicate reveal_event_format

[@@ "opaque_to_smt"]
val trigger_reveal_event :
  principal -> principal -> timestamp ->
  traceful unit
let trigger_reveal_event by_principal to nonce_at =
  trigger_event by_principal {to=to; point=nonce_at;}

[@@ "opaque_to_smt"]
val reveal_event_triggered_at :
  trace -> timestamp -> principal -> principal -> timestamp ->
  prop
let reveal_event_triggered_at tr i prin reveal_to nonce_at =
  event_triggered_at tr i prin {to=reveal_to; point=nonce_at}

val reveal_event_triggered :
  trace -> principal -> principal -> timestamp ->
  prop
let reveal_event_triggered tr prin reveal_to nonce_at =
  exists i. reveal_event_triggered_at tr i prin reveal_to nonce_at

(**
    The below definitions here may be redundant.
    They all require just a reveal_opaque of reveal_event and then the lemmas in DY.Lib.Event.Typed trigger to prove the required facts.
**)

val trigger_reveal_event_reveal_event_triggered :
  prin:principal -> reveal_to:principal -> nonce_at:timestamp -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = trigger_reveal_event prin reveal_to nonce_at tr in
    reveal_event_triggered tr_out prin reveal_to nonce_at
  ))
let trigger_reveal_event_reveal_event_triggered prin reveal_to nonce_at tr =
  reveal_opaque (`%trigger_reveal_event) (trigger_reveal_event);
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at)

val trigger_reveal_event_trace_invariant :
  {|protocol_invariants|} ->
  epred:reveal_event_predicate ->
  prin:principal -> reveal_to:principal -> nonce_at:timestamp -> tr:trace ->
  Lemma
  (requires
    epred tr prin {to=reveal_to; point=nonce_at} /\
    has_event_pred epred /\
    trace_invariant tr
  )
  (ensures (
    let ((), tr_out) = trigger_reveal_event prin reveal_to nonce_at tr in
    trace_invariant tr_out
  ))
  [SMTPat (trigger_reveal_event prin reveal_to nonce_at);
   SMTPat (has_event_pred epred);
   SMTPat (trace_invariant tr)]
let trigger_reveal_event_trace_invariant #invs epred prin reveal_to nonce_at tr =
  reveal_opaque (`%trigger_reveal_event) (trigger_reveal_event)

val reveal_event_triggered_at_on_trace :
  tr:trace ->
  i:timestamp -> prin:principal -> reveal_to:principal -> nonce_at:timestamp ->
  Lemma
  (requires
    reveal_event_triggered_at tr i prin reveal_to nonce_at
  )
  (ensures i `on_trace` tr)
  [SMTPat (reveal_event_triggered_at tr i prin reveal_to nonce_at)]
let reveal_event_triggered_at_on_trace tr i prin reveal_to nonce_at =
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at)

val reveal_event_triggered_at_implies_pred:
  {|protocol_invariants|} ->
  epred:reveal_event_predicate -> tr:trace ->
  i:timestamp -> prin:principal -> reveal_to:principal -> nonce_at:timestamp ->
  Lemma
  (requires
    reveal_event_triggered_at tr i prin reveal_to nonce_at /\
    has_event_pred epred /\
    trace_invariant tr
  )
  (ensures epred (prefix tr i) prin {to=reveal_to; point=nonce_at})
  [SMTPat (reveal_event_triggered_at tr i prin reveal_to nonce_at);
   SMTPat (has_event_pred epred);
   SMTPat (trace_invariant tr);
  ]
let reveal_event_triggered_at_implies_pred #invs epred tr i prin reveal_to nonce_at =
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at)

// Proof requires an assertion to build the record so that event_triggered_grows is invoked.
val reveal_event_triggered_grows:
  tr1:trace -> tr2:trace ->
  prin:principal -> reveal_to:principal -> nonce_at:timestamp ->
  Lemma
  (requires reveal_event_triggered tr1 prin reveal_to nonce_at /\ tr1 <$ tr2)
  (ensures reveal_event_triggered tr2 prin reveal_to nonce_at)
  [SMTPat (reveal_event_triggered tr1 prin reveal_to nonce_at); SMTPat (tr1 <$ tr2)]
let reveal_event_triggered_grows tr1 tr2 prin reveal_to nonce_at =
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at);
  assert(event_triggered tr1 prin {to=reveal_to; point=nonce_at;})


val reveal_event_triggered_at_implies_trace_entry_at:
  tr:trace -> i:timestamp -> prin:principal -> reveal_to:principal -> nonce_at:timestamp ->
  Lemma
  (requires reveal_event_triggered_at tr i prin reveal_to nonce_at)
  (ensures (
    let e = {to=reveal_to; point=nonce_at;} in
    get_entry_at tr i == Event prin reveal_event.tag (serialize reveal_event_format e) /\
    parse #bytes reveal_event_format (serialize reveal_event_format e) == Some e
  ))
  [SMTPat (reveal_event_triggered_at tr i prin reveal_to nonce_at)]
let reveal_event_triggered_at_implies_trace_entry_at tr i prin reveal_to nonce_at =
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at)


[@@ "opaque_to_smt"]
val find_reveal_event_triggered_at_timestamp:
  tr:trace ->
  prin:principal -> reveal_to:principal -> nonce_at:timestamp ->
  Pure timestamp
  (requires reveal_event_triggered tr prin reveal_to nonce_at)
  (ensures fun i ->
    reveal_event_triggered_at tr i prin reveal_to nonce_at /\
    ~(reveal_event_triggered (prefix tr i) prin reveal_to nonce_at)
  )
let find_reveal_event_triggered_at_timestamp tr prin reveal_to nonce_at =
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at);
  find_event_triggered_at_timestamp tr prin {to=reveal_to; point=nonce_at;}

val find_reveal_event_triggered_at_timestamp_later:
  tr1:trace -> tr2:trace ->
  prin:principal -> reveal_to:principal -> nonce_at:timestamp ->
  Lemma
  (requires
    reveal_event_triggered tr1 prin reveal_to nonce_at /\
    tr1 <$ tr2
  )
  (ensures find_reveal_event_triggered_at_timestamp tr1 prin reveal_to nonce_at == find_reveal_event_triggered_at_timestamp tr2 prin reveal_to nonce_at)
  [SMTPat (find_reveal_event_triggered_at_timestamp tr1 prin reveal_to nonce_at);
   SMTPat (find_reveal_event_triggered_at_timestamp tr2 prin reveal_to nonce_at);
   SMTPat (tr1 <$ tr2)
  ]
let find_reveal_event_triggered_at_timestamp_later tr1 tr2 prin reveal_to nonce_at =
  reveal_opaque (`%find_reveal_event_triggered_at_timestamp) (find_reveal_event_triggered_at_timestamp);
  reveal_opaque (`%reveal_event_triggered_at) (reveal_event_triggered_at);
  find_event_triggered_at_timestamp_later tr1 tr2 prin {to=reveal_to; point=nonce_at;}

(**
   Some kind of predicate for a reveal event.

  | RevealLabel prin time ->
    exists b. rand_generated_at tr time b
    // There exists some bytes generated at this timestamp
    // potential for custom predicates here i.e:
    // invs.trace_invs.reveal_pred tr prin time

)
