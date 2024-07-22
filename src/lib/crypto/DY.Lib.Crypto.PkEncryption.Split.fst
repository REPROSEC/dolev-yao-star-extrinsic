module DY.Lib.Crypto.PkEncryption.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.SplitFunction

let split_pkenc_predicate_params (cusages:crypto_usages) = {
  singleton_split_function_parameters string with

  tagged_data_t = (trace & (pk:bytes{PkdecKey? (get_sk_usage pk)}) & bytes);
  raw_data_t = (trace & (pk:bytes{PkdecKey? (get_sk_usage pk)}) & bytes);
  output_t = prop;

  decode_tagged_data = (fun (tr, pk, msg) ->
    let PkdecKey tag _ = get_sk_usage pk in
    Some (tag, (tr, pk, msg))
  );

  local_fun_t = pkenc_crypto_predicate cusages;
  global_fun_t = trace -> pk:bytes{PkdecKey? (get_sk_usage pk)} -> msg:bytes -> prop;

  default_global_fun = (fun tr pk msg -> False);

  apply_local_fun = (fun pred (tr, pk, msg) ->
    pred.pred tr pk msg
  );
  apply_global_fun = (fun pred (tr, pk, msg) ->
    pred tr pk msg
  );
  mk_global_fun = (fun pred tr pk msg ->
    pred (tr, pk, msg)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

val has_pkenc_predicate: cinvs:crypto_invariants -> (string & pkenc_crypto_predicate cinvs.usages) -> prop
let has_pkenc_predicate cinvs (tag, pred) =
  has_local_fun (split_pkenc_predicate_params cinvs.usages) pkenc_pred.pred (tag, pred)

(*** Global pkenc predicate builder ***)

val mk_global_pkenc_predicate:
  {|cusgs:crypto_usages|} ->
  list (string & pkenc_crypto_predicate cusgs) ->
  trace -> pk:bytes{PkdecKey? (get_sk_usage pk)} -> msg:bytes -> prop
let mk_global_pkenc_predicate #cusgs l =
  mk_global_fun (split_pkenc_predicate_params cusgs) l

val mk_global_pkenc_predicate_correct:
  cinvs:crypto_invariants -> lpreds:list (string & pkenc_crypto_predicate cinvs.usages) ->
  Lemma
  (requires
    pkenc_pred.pred == mk_global_pkenc_predicate lpreds /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds)
  )
  (ensures for_allP (has_pkenc_predicate cinvs) lpreds)
let mk_global_pkenc_predicate_correct cinvs lpreds =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst lpreds);
  for_allP_eq (has_pkenc_predicate cinvs) lpreds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct (split_pkenc_predicate_params cinvs.usages) lpreds))

val mk_global_pkenc_predicate_later:
  {|cusgs:crypto_usages|} -> lpreds:list (string & pkenc_crypto_predicate cusgs) ->
  tr1:trace -> tr2:trace -> pk:bytes{PkdecKey? (get_sk_usage pk)} -> msg:bytes ->
  Lemma
  (requires mk_global_pkenc_predicate lpreds tr1 pk msg  /\ tr1 <$ tr2)
  (ensures mk_global_pkenc_predicate lpreds tr2 pk msg)
let mk_global_pkenc_predicate_later #cusgs lpreds tr1 tr2 pk msg  =
  mk_global_fun_eq (split_pkenc_predicate_params cusgs) lpreds (tr1, pk, msg);
  mk_global_fun_eq (split_pkenc_predicate_params cusgs) lpreds (tr2, pk, msg);
  introduce forall lpred. (split_pkenc_predicate_params cusgs).apply_local_fun lpred (tr1, pk, msg) ==> (split_pkenc_predicate_params cusgs).apply_local_fun lpred (tr2, pk, msg) with (
    introduce _ ==> _ with _. lpred.pred_later tr1 tr2 pk msg
  )

val mk_pkenc_predicate: {|cusgs:crypto_usages|} -> list (string & pkenc_crypto_predicate cusgs) -> pkenc_crypto_predicate cusgs
let mk_pkenc_predicate #cusgs lpreds = {
  pred = mk_global_pkenc_predicate lpreds;
  pred_later = mk_global_pkenc_predicate_later lpreds;
}
