module DY.Example.SingleMessage.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleMessage.Protocol.Total
open DY.Example.SingleMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

val crypto_usages_protocol: crypto_usages
instance crypto_usages_protocol = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
(*val crypto_predicates_protocol: crypto_predicates crypto_usages_protocol
let crypto_predicates_protocol = {
  default_crypto_predicates crypto_usages_protocol with

  pkenc_pred = (fun tr pk msg ->
    get_sk_usage pk == PkdecKey "DY.Lib.Communication.PublicKey" /\
    (exists client server. get_sk_label pk = principal_label server /\
      (match parse message msg with
      | Some (Msg msg) -> (
        event_triggered tr client (ClientSendMsg client server msg.secret) /\ 
        get_label msg.secret == join (principal_label client) (principal_label server)
      )
      | None -> False)
    )
  );
  pkenc_pred_later = (fun tr1 tr2 pk msg -> ());
}

val crypto_preds_protocol: higher_layer_preds_type
let crypto_preds_protocol tr pk payload client server =
  match parse message payload with
      | Some (Msg msg) -> (
        event_triggered tr client (ClientSendMsg client server msg.secret)
      )
      | None -> False
*)

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = build_crypto_predicates (fun tr pk msg -> False);
}
#pop-options

(*** Proofs ***)

val compute_message_proof:
  tr:trace ->
  client:principal -> server:principal ->
  secret:bytes ->
  Lemma
  (requires
    event_triggered tr client (ClientSendMsg client server secret) /\
    bytes_invariant tr secret /\
    is_knowable_by (join (principal_label client) (principal_label server)) tr secret
  )
  (ensures
    is_knowable_by (join (principal_label client) (principal_label server)) tr (compute_message secret)
  )
let compute_message_proof tr client server secret =
  serialize_wf_lemma message (is_knowable_by (join (principal_label client) (principal_label server)) tr) (Msg {secret;});
  ()

val decode_message_proof:
  tr:trace ->
  client:principal -> server:principal ->
  msg_bytes:bytes ->
  Lemma
  (requires
    is_knowable_by (join (principal_label client) (principal_label server)) tr msg_bytes \/
    is_publishable tr msg_bytes
  )
  (ensures (
    match decode_message msg_bytes with
    | Some msg -> (
      is_knowable_by (join (principal_label client) (principal_label server)) tr msg.secret
    )
    | None -> True
  )
  )
let decode_message_proof tr client server msg_bytes =
  match decode_message msg_bytes with
  | Some msg -> (
    parse_wf_lemma message (is_knowable_by (join (principal_label client) (principal_label server)) tr) msg_bytes;
    ()
  )
  | None -> ()
