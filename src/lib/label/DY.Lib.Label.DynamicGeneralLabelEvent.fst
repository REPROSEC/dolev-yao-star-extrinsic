module DY.Lib.Label.DynamicGeneralLabelEvent

open Comparse
open DY.Core
open DY.Lib.Event.Typed
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

[@@ with_bytes bytes]
type reveal_general_event_format = {
  new_label:bytes;
  [@@@ with_parser #bytes ps_timestamp]
  point:timestamp;
}

%splice [ps_reveal_general_event_format] (gen_parser (`reveal_general_event_format))
%splice [ps_reveal_general_event_format_is_well_formed] (gen_is_well_formed_lemma (`reveal_general_event_format))

instance parseable_serializeable_bytes_reveal_general_event_format: parseable_serializeable bytes reveal_general_event_format =
  mk_parseable_serializeable ps_reveal_general_event_format

instance reveal_general_event : event reveal_general_event_format = mk_event_instance "GeneralReveal"

let reveal_general_event_predicate = event_predicate reveal_general_event_format

let default_reveal_event_predicate (#crypto_invs:crypto_invariants) : reveal_general_event_predicate =
  fun tr prin a ->
    exists (b:bytes).
      (
        (
          is_knowable_by (principal_label prin) tr b \/
          is_publishable tr b \/
          get_label tr (a.new_label) == principal_label prin // this is a generalized version of the initial reveal (the creator of a secret must reveal it to themselves initially (and they therefore can't 'know' it at this point))
        ) /\
        (
          rand_generated_at tr a.point b \/
          is_publishable tr b // if the bytes we would like to reveal are publishable, then we can reveal to whomever.
        )
      )

(*** Reveal Event Definitions ***)

[@@ "opaque_to_smt"]
val trigger_reveal_general_event :
  principal -> bytes -> timestamp ->
  traceful unit
let trigger_reveal_general_event by_principal new_label_bytes nonce_at =
  trigger_event by_principal {new_label=new_label_bytes; point=nonce_at;}

[@@ "opaque_to_smt"]
val reveal_general_event_triggered_at :
  trace -> timestamp -> principal -> bytes -> timestamp ->
  prop
let reveal_general_event_triggered_at tr i prin new_label_bytes nonce_at =
  event_triggered_at tr i prin {new_label=new_label_bytes; point=nonce_at}

val reveal_general_event_triggered :
  trace -> principal -> bytes -> timestamp ->
  prop
let reveal_general_event_triggered tr prin new_label_bytes nonce_at =
  exists i. reveal_general_event_triggered_at tr i prin new_label_bytes nonce_at
