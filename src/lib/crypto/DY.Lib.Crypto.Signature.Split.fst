module DY.Lib.Crypto.Signature.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_sign_predicate_params {|crypto_usages|}: split_crypto_predicate_parameters = {
  key_t = sk_usage:usage{SigKey? sk_usage};
  data_t = bytes;
  get_usage = (fun vk_usg ->
    let SigKey tag _ = vk_usg in
    tag
  );

  local_pred_t = sign_crypto_predicate;
  global_pred_t = tr:trace -> sk_usage:usage{SigKey? sk_usage} -> msg:bytes -> prop;

  apply_local_pred = (fun pred (tr, sk_usage, msg) ->
    pred.pred tr sk_usage msg
  );
  apply_global_pred = (fun pred (tr, sk_usage, msg) ->
    pred tr sk_usage msg
  );
  mk_global_pred = (fun pred tr sk_usage msg ->
    pred (tr, sk_usage, msg)
  );

  key_and_data_well_formed = (fun tr sk_usage msg ->
    bytes_well_formed tr msg
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 sk_usage msg ->
    lpred.pred_later tr1 tr2 sk_usage msg
  );
}

val has_sign_predicate: {|crypto_invariants|} -> (string & sign_crypto_predicate) -> prop
let has_sign_predicate #cinvs (tag, local_pred) =
  forall (tr:trace) (sk_usage:usage) (msg:bytes).
    {:pattern sign_pred.pred tr sk_usage msg}
    match sk_usage with
    | SigKey sign_tag _ ->
        sign_tag = tag ==> sign_pred.pred tr sk_usage msg == local_pred.pred tr sk_usage msg
    | _ -> True

val intro_has_sign_predicate:
  {|crypto_invariants|} -> tagged_local_pred:(string & sign_crypto_predicate) ->
  Lemma
  (requires has_local_crypto_predicate split_sign_predicate_params sign_pred.pred tagged_local_pred)
  (ensures has_sign_predicate tagged_local_pred)
let intro_has_sign_predicate #cinvs (tag, local_pred) =
  introduce
    forall tr sk_usage msg.
      match sk_usage with
      | SigKey sign_tag _ ->
          sign_tag = tag ==> sign_pred.pred tr sk_usage msg == local_pred.pred tr sk_usage msg
      | _ -> True
  with (
    match sk_usage with
    | SigKey sign_tag _ ->
      has_local_crypto_predicate_elim (split_sign_predicate_params) sign_pred.pred tag local_pred tr sk_usage msg
    | _ -> ()
  )

(*** Global sign predicate builder ***)

val mk_sign_predicate:
  {|crypto_usages|} ->
  list (string & sign_crypto_predicate) ->
  sign_crypto_predicate
let mk_sign_predicate #cusgs l = {
  pred = mk_global_crypto_predicate split_sign_predicate_params l;
  pred_later = mk_global_crypto_predicate_later split_sign_predicate_params l;
}

val mk_sign_predicate_correct:
  {|crypto_invariants|} -> tagged_local_preds:list (string & sign_crypto_predicate) ->
  Lemma
  (requires
    sign_pred == mk_sign_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP has_sign_predicate tagged_local_preds)
let mk_sign_predicate_correct #cinvs tagged_local_preds =
  for_allP_eq has_sign_predicate tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct split_sign_predicate_params tagged_local_preds));
  FStar.Classical.forall_intro (FStar.Classical.move_requires intro_has_sign_predicate)
