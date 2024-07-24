module DY.Lib.Crypto.Signature.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_sign_predicate_params (cusages:crypto_usages): split_crypto_predicate_parameters = {
  key_t = vk:bytes{SigKey? (get_signkey_usage vk)};
  data_t = bytes;
  get_usage = (fun pk ->
    let SigKey tag _ = get_signkey_usage pk in
    tag
  );

  local_pred_t = sign_crypto_predicate cusages;
  global_pred_t = tr:trace -> vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes -> prop;

  apply_local_pred = (fun pred (tr, vk, msg) ->
    pred.pred tr vk msg
  );
  apply_global_pred = (fun pred (tr, vk, msg) ->
    pred tr vk msg
  );
  mk_global_pred = (fun pred tr vk msg ->
    pred (tr, vk, msg)
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 vk msg ->
    lpred.pred_later tr1 tr2 vk msg
  );
}

val has_sign_predicate: cinvs:crypto_invariants -> (string & sign_crypto_predicate cinvs.usages) -> prop
let has_sign_predicate cinvs (tag, pred) =
  has_local_crypto_predicate (split_sign_predicate_params cinvs.usages) sign_pred.pred (tag, pred)

(*** Global sign predicate builder ***)

val mk_sign_predicate:
  {|cusgs:crypto_usages|} ->
  list (string & sign_crypto_predicate cusgs) ->
  sign_crypto_predicate cusgs
let mk_sign_predicate #cusgs l = {
  pred = mk_global_crypto_predicate (split_sign_predicate_params cusgs) l;
  pred_later = mk_global_crypto_predicate_later (split_sign_predicate_params cusgs) l;
}

val mk_sign_predicate_correct:
  cinvs:crypto_invariants -> tagged_local_preds:list (string & sign_crypto_predicate cinvs.usages) ->
  Lemma
  (requires
    sign_pred == mk_sign_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP (has_sign_predicate cinvs) tagged_local_preds)
let mk_sign_predicate_correct cinvs tagged_local_preds =
  for_allP_eq (has_sign_predicate cinvs) tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct (split_sign_predicate_params cinvs.usages) tagged_local_preds))
