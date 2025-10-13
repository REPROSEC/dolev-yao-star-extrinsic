module DY.Lib.Label.DynamicBytesLabelEvent

open Comparse
open DY.Core
open DY.Lib.Event.Typed
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

[@@ with_bytes bytes]
type reveal_to_bytes_label_event_format = {
  bytes_label:bytes;
  [@@@ with_parser #bytes ps_timestamp]
  point:timestamp;
}

%splice [ps_reveal_to_bytes_label_event_format] (gen_parser (`reveal_to_bytes_label_event_format))
%splice [ps_reveal_to_bytes_label_event_format_is_well_formed] (gen_is_well_formed_lemma (`reveal_to_bytes_label_event_format))

instance parseable_serializeable_bytes_reveal_general_event_format: parseable_serializeable bytes reveal_to_bytes_label_event_format =
  mk_parseable_serializeable ps_reveal_to_bytes_label_event_format

instance reveal_to_bytes_label_event : event reveal_to_bytes_label_event_format = mk_event_instance "GeneralReveal"

noeq
type reveal_to_bytes_label_event_predicate {|crypto_invariants|} =
  {
    pred : event_predicate reveal_to_bytes_label_event_format;
    pred_knowable :
      tr:trace -> prin:principal -> ev:reveal_to_bytes_label_event_format ->
      Lemma
      (requires pred tr prin ev)
      (ensures (
        is_knowable_by (principal_label prin) tr ev.bytes_label /\
        exists b.
          (
            rand_generated_at tr ev.point b /\
            (
              is_knowable_by (principal_label prin) tr b \/
              rand_just_generated tr b
            )
          ) \/
          is_publishable tr b
      ));

  }

let default_reveal_event_predicate (#crypto_invs:crypto_invariants) : reveal_to_bytes_label_event_predicate
  = {
  pred = (fun tr prin a ->
    is_knowable_by (principal_label prin) tr a.bytes_label /\
    exists (b:bytes).
      (
        rand_generated_at tr a.point b /\
        (
          is_knowable_by (principal_label prin) tr b \/
          rand_just_generated tr b
        )
      ) \/
      is_publishable tr b
  );
  pred_knowable = fun tr prin a -> ()
}

(*** Reveal Event Definitions ***)

[@@ "opaque_to_smt"]
val trigger_reveal_to_bytes_label_event :
  principal -> bytes -> timestamp ->
  traceful unit
let trigger_reveal_to_bytes_label_event by_principal new_label_bytes nonce_at =
  trigger_event by_principal {bytes_label=new_label_bytes; point=nonce_at;}

[@@ "opaque_to_smt"]
val reveal_to_bytes_label_event_triggered_at :
  trace -> timestamp -> principal -> bytes -> timestamp ->
  prop
let reveal_to_bytes_label_event_triggered_at tr i prin new_label_bytes nonce_at =
  event_triggered_at tr i prin {bytes_label=new_label_bytes; point=nonce_at}

val reveal_to_bytes_label_event_triggered :
  trace -> principal -> bytes -> timestamp ->
  prop
let reveal_to_bytes_label_event_triggered tr prin new_label_bytes nonce_at =
  exists i. reveal_to_bytes_label_event_triggered_at tr i prin new_label_bytes nonce_at
