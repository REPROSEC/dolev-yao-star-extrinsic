module DY.Lib.Crypto.Signature.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.SplitFunction

let split_sign_predicate_params (cusages:crypto_usages) = {
  singleton_split_function_parameters string with

  tagged_data_t = (trace & (vk:bytes{SigKey? (get_signkey_usage vk)}) & bytes);
  raw_data_t = (trace & (vk:bytes{SigKey? (get_signkey_usage vk)}) & bytes);
  output_t = prop;

  decode_tagged_data = (fun (tr, vk, msg) ->
    let SigKey tag _ = get_signkey_usage vk in
    Some (tag, (tr, vk, msg))
  );

  local_fun_t = sign_crypto_predicate cusages;
  global_fun_t = trace -> vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes -> prop;

  default_global_fun = (fun tr vk msg -> False);

  apply_local_fun = (fun pred (tr, vk, msg) ->
    pred.pred tr vk msg
  );
  apply_global_fun = (fun pred (tr, vk, msg) ->
    pred tr vk msg
  );
  mk_global_fun = (fun pred tr vk msg ->
    pred (tr, vk, msg)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

val has_sign_predicate: cinvs:crypto_invariants -> (string & sign_crypto_predicate cinvs.usages) -> prop
let has_sign_predicate cinvs (tag, pred) =
  has_local_fun (split_sign_predicate_params cinvs.usages) sign_pred.pred (tag, pred)

(*** Global sign predicate builder ***)

val mk_global_sign_predicate:
  {|cusgs:crypto_usages|} ->
  list (string & sign_crypto_predicate cusgs) ->
  trace -> vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes -> prop
let mk_global_sign_predicate #cusgs l =
  mk_global_fun (split_sign_predicate_params cusgs) l

val mk_global_sign_predicate_correct:
  cinvs:crypto_invariants -> tagged_local_preds:list (string & sign_crypto_predicate cinvs.usages) ->
  Lemma
  (requires
    sign_pred.pred == mk_global_sign_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP (has_sign_predicate cinvs) tagged_local_preds)
let mk_global_sign_predicate_correct cinvs tagged_local_preds =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst tagged_local_preds);
  for_allP_eq (has_sign_predicate cinvs) tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct (split_sign_predicate_params cinvs.usages) tagged_local_preds))

val mk_global_sign_predicate_later:
  {|cusgs:crypto_usages|} -> tagged_local_preds:list (string & sign_crypto_predicate cusgs) ->
  tr1:trace -> tr2:trace -> vk:bytes{SigKey? (get_signkey_usage vk)} -> msg:bytes ->
  Lemma
  (requires mk_global_sign_predicate tagged_local_preds tr1 vk msg  /\ tr1 <$ tr2)
  (ensures mk_global_sign_predicate tagged_local_preds tr2 vk msg)
let mk_global_sign_predicate_later #cusgs tagged_local_preds tr1 tr2 vk msg  =
  mk_global_fun_eq (split_sign_predicate_params cusgs) tagged_local_preds (tr1, vk, msg);
  mk_global_fun_eq (split_sign_predicate_params cusgs) tagged_local_preds (tr2, vk, msg);
  introduce forall lpred. (split_sign_predicate_params cusgs).apply_local_fun lpred (tr1, vk, msg) ==> (split_sign_predicate_params cusgs).apply_local_fun lpred (tr2, vk, msg) with (
    introduce _ ==> _ with _. lpred.pred_later tr1 tr2 vk msg
  )

val mk_sign_predicate: {|cusgs:crypto_usages|} -> list (string & sign_crypto_predicate cusgs) -> sign_crypto_predicate cusgs
let mk_sign_predicate #cusgs tagged_local_preds = {
  pred = mk_global_sign_predicate tagged_local_preds;
  pred_later = mk_global_sign_predicate_later tagged_local_preds;
}
