module DY.Lib.Crypto.AEAD.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.SplitFunction

let split_aead_predicate_params (cusages:crypto_usages) = {
  singleton_split_function_parameters string with

  tagged_data_t = (trace & (key:bytes{AeadKey? (get_usage key)}) & bytes & bytes);
  raw_data_t = (trace & (key:bytes{AeadKey? (get_usage key)}) & bytes & bytes);
  output_t = prop;

  decode_tagged_data = (fun (tr, key, msg, ad) ->
    let AeadKey tag _ = get_usage key in
    Some (tag, (tr, key, msg, ad))
  );

  local_fun_t = aead_crypto_predicate cusages;
  global_fun_t = trace -> key:bytes{AeadKey? (get_usage key)} -> msg:bytes -> ad:bytes -> prop;

  default_global_fun = (fun tr key msg ad -> False);

  apply_local_fun = (fun pred (tr, key, msg, ad) ->
    pred.pred tr key msg ad
  );
  apply_global_fun = (fun pred (tr, key, msg, ad) ->
    pred tr key msg ad
  );
  mk_global_fun = (fun pred tr key msg ad ->
    pred (tr, key, msg, ad)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

val has_aead_predicate: cinvs:crypto_invariants -> (string & aead_crypto_predicate cinvs.usages) -> prop
let has_aead_predicate cinvs (tag, pred) =
  has_local_fun (split_aead_predicate_params cinvs.usages) aead_pred.pred (tag, pred)

(*** Global aead predicate builder ***)

val mk_global_aead_predicate:
  {|cusgs:crypto_usages|} ->
  list (string & aead_crypto_predicate cusgs) ->
  trace -> key:bytes{AeadKey? (get_usage key)} -> msg:bytes -> ad:bytes -> prop
let mk_global_aead_predicate #cusgs l =
  mk_global_fun (split_aead_predicate_params cusgs) l

val mk_global_aead_predicate_correct:
  cinvs:crypto_invariants -> lpreds:list (string & aead_crypto_predicate cinvs.usages) ->
  Lemma
  (requires
    aead_pred.pred == mk_global_aead_predicate lpreds /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds)
  )
  (ensures for_allP (has_aead_predicate cinvs) lpreds)
let mk_global_aead_predicate_correct cinvs lpreds =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst lpreds);
  for_allP_eq (has_aead_predicate cinvs) lpreds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct (split_aead_predicate_params cinvs.usages) lpreds))

val mk_global_aead_predicate_later:
  {|cusgs:crypto_usages|} -> lpreds:list (string & aead_crypto_predicate cusgs) ->
  tr1:trace -> tr2:trace -> key:bytes{AeadKey? (get_usage key)} -> msg:bytes -> ad:bytes ->
  Lemma
  (requires mk_global_aead_predicate lpreds tr1 key msg ad /\ tr1 <$ tr2)
  (ensures mk_global_aead_predicate lpreds tr2 key msg ad)
let mk_global_aead_predicate_later #cusgs lpreds tr1 tr2 key msg ad =
  mk_global_fun_eq (split_aead_predicate_params cusgs) lpreds (tr1, key, msg, ad);
  mk_global_fun_eq (split_aead_predicate_params cusgs) lpreds (tr2, key, msg, ad);
  introduce forall lpred. (split_aead_predicate_params cusgs).apply_local_fun lpred (tr1, key, msg, ad) ==> (split_aead_predicate_params cusgs).apply_local_fun lpred (tr2, key, msg, ad) with (
    introduce _ ==> _ with _. lpred.pred_later tr1 tr2 key msg ad
  )

val mk_aead_predicate: {|cusgs:crypto_usages|} -> list (string & aead_crypto_predicate cusgs) -> aead_crypto_predicate cusgs
let mk_aead_predicate #cusgs lpreds = {
  pred = mk_global_aead_predicate lpreds;
  pred_later = mk_global_aead_predicate_later lpreds;
}
