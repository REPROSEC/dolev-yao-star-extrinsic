module DY.Example.DH.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total
open DY.Example.DH.Protocol.Stateful

(*** Cryptographic invariants ***)

val dh_crypto_usages: crypto_usages
instance dh_crypto_usages = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
val dh_crypto_preds: crypto_predicates dh_crypto_usages
let dh_crypto_preds = {
  default_crypto_predicates dh_crypto_usages with

  sign_pred = (fun tr vk sig_msg -> 
    get_signkey_usage vk == SigKey "DH.SigningKey" /\
    (exists prin. get_signkey_label vk = principal_label prin /\ (
      match parse sig_message sig_msg with
      | Some (SigMsg2 sig_msg2) -> (
        exists y. sig_msg2.gy == (dh_pk y) /\ event_triggered tr prin (Respond1 sig_msg2.a prin sig_msg2.gx sig_msg2.gy y)
      )
      | Some (SigMsg3 sig_msg3) -> (
        exists x. sig_msg3.gx == (dh_pk x) /\ event_triggered tr prin (Initiate2 prin sig_msg3.b sig_msg3.gx sig_msg3.gy x)
      )
      | None -> False
    ))
  );
  sign_pred_later = (fun tr1 tr2 vk msg -> ())
}
#pop-options

instance dh_crypto_invs = {
  usages = dh_crypto_usages;
  preds = dh_crypto_preds;
}

(*** Proofs ***)