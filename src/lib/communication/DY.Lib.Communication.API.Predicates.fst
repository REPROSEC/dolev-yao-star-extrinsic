module DY.Lib.Communication.API.Predicates

open Comparse
open DY.Core
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Event.Typed

open DY.Lib.Communication.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic Predicates ***)

// TODO add higher layer preds as a parameter
#push-options "--ifuel 2 --fuel 0"
val pkenc_crypto_predicates_communication_layer: cusages:crypto_usages -> pkenc_crypto_predicate cusages
let pkenc_crypto_predicates_communication_layer cusages = {
  pred = (fun tr pk msg ->
    get_sk_usage pk == PkKey comm_layer_tag empty /\
      (match parse communication_message msg with
      | Some {sender; receiver; payload} -> (
        get_sk_label pk == principal_label receiver /\
        (get_label payload) `can_flow tr` (join (principal_label sender) (principal_label receiver))
      )
      | None -> False)
    );
  pred_later = (fun tr1 tr2 pk msg -> ());
}
#pop-options

val pkenc_crypto_predicates_communication_layer_and_tag: 
  {|cusages:crypto_usages|} ->
  (string & pkenc_crypto_predicate cusages)
let pkenc_crypto_predicates_communication_layer_and_tag #cusages = 
  (comm_layer_tag, pkenc_crypto_predicates_communication_layer cusages)

val has_communication_layer_invariants:
  crypto_invariants ->
  prop
let has_communication_layer_invariants cinvs =
  has_pkenc_predicate cinvs pkenc_crypto_predicates_communication_layer_and_tag

(*** Event Predicates ***)

#push-options "--ifuel 1 --fuel 0"
let event_predicate_communication_layer {|cinvs:crypto_invariants|} : event_predicate communication_event =
  fun tr prin e ->
    match e with
    | CommunicationLayerSendMsg sender receiver payload -> True
    | CommunicationLayerReceiveMsg sender receiver payload -> True
#pop-options
