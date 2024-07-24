module DY.Lib.Crypto.PkEncryption.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_pkenc_predicate_params (cusages:crypto_usages): split_crypto_predicate_parameters = {
  key_t = pk:bytes{PkKey? (get_sk_usage pk)};
  data_t = bytes;
  get_usage = (fun pk ->
    let PkKey tag _ = get_sk_usage pk in
    tag
  );

  local_pred_t = pkenc_crypto_predicate cusages;
  global_pred_t = tr:trace -> pk:bytes{PkKey? (get_sk_usage pk)} -> msg:bytes -> prop;

  apply_local_pred = (fun pred (tr, pk, msg) ->
    pred.pred tr pk msg
  );
  apply_global_pred = (fun pred (tr, pk, msg) ->
    pred tr pk msg
  );
  mk_global_pred = (fun pred tr pk msg ->
    pred (tr, pk, msg)
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 pk msg ->
    lpred.pred_later tr1 tr2 pk msg
  );
}

val has_pkenc_predicate: cinvs:crypto_invariants -> (string & pkenc_crypto_predicate cinvs.usages) -> prop
let has_pkenc_predicate cinvs (tag, pred) =
  has_local_crypto_predicate (split_pkenc_predicate_params cinvs.usages) pkenc_pred.pred (tag, pred)

(*** Global pkenc predicate builder ***)

val mk_pkenc_predicate:
  {|cusgs:crypto_usages|} ->
  list (string & pkenc_crypto_predicate cusgs) ->
  pkenc_crypto_predicate cusgs
let mk_pkenc_predicate #cusgs l = {
  pred = mk_global_crypto_predicate (split_pkenc_predicate_params cusgs) l;
  pred_later = mk_global_crypto_predicate_later (split_pkenc_predicate_params cusgs) l;
}

val mk_pkenc_predicate_correct:
  cinvs:crypto_invariants -> tagged_local_preds:list (string & pkenc_crypto_predicate cinvs.usages) ->
  Lemma
  (requires
    pkenc_pred == mk_pkenc_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP (has_pkenc_predicate cinvs) tagged_local_preds)
let mk_pkenc_predicate_correct cinvs tagged_local_preds =
  for_allP_eq (has_pkenc_predicate cinvs) tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct (split_pkenc_predicate_params cinvs.usages) tagged_local_preds))
