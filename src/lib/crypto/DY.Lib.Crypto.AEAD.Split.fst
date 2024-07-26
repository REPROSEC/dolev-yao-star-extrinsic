module DY.Lib.Crypto.AEAD.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_aead_predicate_params (cusages:crypto_usages): split_crypto_predicate_parameters = {
  key_t = key:bytes{AeadKey? (get_usage key)};
  data_t = (bytes & bytes & bytes);
  get_usage = (fun key ->
    let AeadKey tag _ = get_usage key in
    tag
  );

  local_pred_t = aead_crypto_predicate cusages;
  global_pred_t = trace -> key:bytes{AeadKey? (get_usage key)} -> nonce:bytes -> msg:bytes -> ad:bytes -> prop;

  apply_local_pred = (fun pred (tr, key, (nonce, msg, ad)) ->
    pred.pred tr key nonce msg ad
  );
  apply_global_pred = (fun pred (tr, key, (nonce, msg, ad)) ->
    pred tr key nonce msg ad
  );
  mk_global_pred = (fun pred tr key nonce msg ad ->
    pred (tr, key, (nonce, msg, ad))
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 key (nonce, msg, ad) ->
    lpred.pred_later tr1 tr2 key nonce msg ad
  );
}

val has_aead_predicate: cinvs:crypto_invariants -> (string & aead_crypto_predicate cinvs.usages) -> prop
let has_aead_predicate cinvs (tag, local_pred) =
  forall (tr:trace) (key:bytes) (nonce:bytes) (msg:bytes) (ad:bytes).
    {:pattern aead_pred.pred tr key nonce msg ad}
    match get_usage key with
    | AeadKey aead_tag _ ->
        aead_tag = tag ==> aead_pred.pred tr key nonce msg ad == local_pred.pred tr key nonce msg ad
    | _ -> True

val intro_has_aead_predicate:
  cinvs:crypto_invariants -> tagged_local_pred:(string & aead_crypto_predicate cinvs.usages) ->
  Lemma
  (requires has_local_crypto_predicate (split_aead_predicate_params cinvs.usages) aead_pred.pred tagged_local_pred)
  (ensures has_aead_predicate cinvs tagged_local_pred)
let intro_has_aead_predicate cinvs (tag, local_pred) =
  introduce
    forall tr key nonce msg ad.
      match get_usage key with
      | AeadKey aead_tag _ ->
          aead_tag = tag ==> aead_pred.pred tr key nonce msg ad == local_pred.pred tr key nonce msg ad
      | _ -> True
  with (
    match get_usage key with
    | AeadKey aead_tag _ ->
      has_local_crypto_predicate_elim (split_aead_predicate_params cinvs.usages) cinvs.preds.aead_pred.pred tag local_pred tr key (nonce, msg, ad)
    | _ -> ()
  )

(*** Global aead predicate builder ***)

val mk_aead_predicate:
  {|cusgs:crypto_usages|} ->
  list (string & aead_crypto_predicate cusgs) ->
  aead_crypto_predicate cusgs
let mk_aead_predicate #cusgs l = {
  pred = mk_global_crypto_predicate (split_aead_predicate_params cusgs) l;
  pred_later = (fun tr1 tr2 key nonce msg ad -> mk_global_crypto_predicate_later (split_aead_predicate_params cusgs) l tr1 tr2 key (nonce, msg, ad));
}

val mk_aead_predicate_correct:
  cinvs:crypto_invariants -> tagged_local_preds:list (string & aead_crypto_predicate cinvs.usages) ->
  Lemma
  (requires
    aead_pred == mk_aead_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP (has_aead_predicate cinvs) tagged_local_preds)
let mk_aead_predicate_correct cinvs tagged_local_preds =
  for_allP_eq (has_aead_predicate cinvs) tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct (split_aead_predicate_params cinvs.usages) tagged_local_preds));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (intro_has_aead_predicate cinvs))
