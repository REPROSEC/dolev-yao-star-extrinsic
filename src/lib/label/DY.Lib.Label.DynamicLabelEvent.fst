module DY.Lib.Label.DynamicLabelEvent

open Comparse
open DY.Core
open DY.Lib.Event.Typed
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

[@@ with_bytes bytes]
type reveal_event_format = {
  [@@@ with_parser #bytes ps_string]
  to:string;
  [@@@ with_parser #bytes ps_timestamp]
  point:timestamp;
}

%splice [ps_reveal_event_format] (gen_parser (`reveal_event_format))
%splice [ps_reveal_event_format_is_well_formed] (gen_is_well_formed_lemma (`reveal_event_format))

instance parseable_serializeable_bytes_reveal_event_format: parseable_serializeable bytes reveal_event_format =
  mk_parseable_serializeable ps_reveal_event_format

instance reveal_event : event reveal_event_format = mk_event_instance "Reveal"

let reveal_event_predicate = event_predicate reveal_event_format

let default_reveal_event_predicate (#crypto_invs:crypto_invariants) : reveal_event_predicate =
  fun tr prin a ->
    exists (b:bytes) (l:pos).
      (
        (
          is_knowable_by (principal_label prin) tr b \/
          a.to = prin // this is for the initial reveal (creator of a secret must reveal it to themselves initially (and they can't 'know' it at this point))
        ) /\
        rand_generated_at tr a.point b
      ) \/
      is_publishable tr b // if the bytes we would like to reveal are publishable, then we can reveal to whomever.

(*** Reveal Event Definitions ***)

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
