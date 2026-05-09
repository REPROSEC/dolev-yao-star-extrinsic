module DY.Example.CCITT.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.CCITT.Protocol.Total

(*** Events ***)

[@@ with_bytes bytes]
type ccitt_event =
  | AliceSends: alice:principal -> bob:principal -> ta:bytes -> na:bytes -> xa:bytes -> ya:bytes -> ccitt_event
  | BobReceives: alice:principal -> bob:principal -> ta:bytes -> na:bytes -> xa:bytes -> ya:bytes -> ccitt_event

%splice [ps_ccitt_event] (gen_parser (`ccitt_event))
%splice [ps_ccitt_event_is_well_formed] (gen_is_well_formed_lemma (`ccitt_event))

instance event_instance: event ccitt_event = {
  tag = "CCITT.Event";
  format = mk_parseable_serializeable ps_ccitt_event;
}

(*** Stateful Functions ***)

val ccitt_sign_tag: string
let ccitt_sign_tag = "CCITT.SignKey"

val ccitt_pke_tag: string
let ccitt_pke_tag = "CCITT.PkeKey"

val ccitt_label: principal -> principal -> label
let ccitt_label p1 p2 = join (principal_label p1) (principal_label p2)

[@@ "opaque_to_smt"]
val alice_send_msg1:
  pki:state_id -> private_keys:state_id ->
  alice:principal -> bob:principal ->
  ta:bytes -> xa:bytes -> ya:bytes ->
  traceful (option timestamp)
let alice_send_msg1 pki private_keys alice bob ta xa ya =
  let*? sk_a = get_private_key alice private_keys (LongTermSigKey ccitt_sign_tag) in
  let*? pk_b = get_public_key alice pki (LongTermPkeKey ccitt_pke_tag) bob in
  let* na = mk_rand NoUsage public 32 in
  let* n_inner_sig = mk_rand SigNonce (long_term_key_label alice) 32 in
  let* n_inner_pke = mk_rand PkeNonce (long_term_key_label alice) 32 in
  let* n_outer = mk_rand SigNonce (long_term_key_label alice) 32 in
  trigger_event alice (AliceSends alice bob ta na xa ya);*
  let msg1 = compute_message1 ta na bob xa ya pk_b sk_a n_inner_sig n_inner_pke n_outer in
  let* msg_id = send_msg msg1 in
  return (Some msg_id)

[@@ "opaque_to_smt"]
val bob_receive_msg1:
  pki:state_id -> private_keys:state_id ->
  bob:principal -> alice:principal ->
  timestamp ->
  traceful (option unit)
let bob_receive_msg1 pki private_keys bob alice msg1_id =
  let*? sk_b = get_private_key bob private_keys (LongTermPkeKey ccitt_pke_tag) in
  let*? vk_a = get_public_key bob pki (LongTermSigKey ccitt_sign_tag) alice in
  let*? msg1_bytes = recv_msg msg1_id in
  let*? (ta, na, bob', xa, ya) = return (decode_message1 bob msg1_bytes sk_b vk_a) in
  // Check that the intended recipient is indeed bob
  if bob' <> bob then return None else (
    trigger_event bob (BobReceives alice bob ta na xa ya);*
    return (Some ())
  )
