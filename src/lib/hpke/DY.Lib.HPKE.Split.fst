module DY.Lib.HPKE.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate
open DY.Lib.HPKE.Lemmas

let split_hpke_predicate_params {|crypto_usages|}: split_crypto_predicate_parameters = {
  key_t = (string & bytes);
  data_t = bytes & bytes & bytes;
  get_usage = (fun (usage_tag, usage_data) ->
    usage_tag
  );

  local_pred_t = hpke_crypto_predicate;
  global_pred_t = tr:trace -> usage:(string & bytes) -> plaintext:bytes -> info:bytes -> ad:bytes -> prop;

  apply_local_pred = (fun pred (tr, usage, (plaintext, info, ad)) ->
    pred.pred tr usage plaintext info ad
  );
  apply_global_pred = (fun pred (tr, usage, (plaintext, info, ad)) ->
    pred tr usage plaintext info ad
  );
  mk_global_pred = (fun pred tr usage plaintext info ad ->
    pred (tr, usage, (plaintext, info, ad))
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 usage (plaintext, info, ad) ->
    lpred.pred_later tr1 tr2 usage plaintext info ad
  );
}

val has_hpke_predicate: {|crypto_usages|} -> {|hpke_crypto_invariants|} -> (string & hpke_crypto_predicate) -> prop
let has_hpke_predicate #cusgs #hpke (tag, local_pred) =
  forall (tr:trace) (usage:(string & bytes)) (plaintext:bytes) (info:bytes) (ad:bytes).
    {:pattern hpke_pred.pred tr usage plaintext info ad}
    fst usage = tag ==> hpke_pred.pred tr usage plaintext info ad == local_pred.pred tr usage plaintext info ad

val intro_has_hpke_predicate:
  {|crypto_usages|} -> {|hpke_crypto_invariants|} ->
  tagged_local_pred:(string & hpke_crypto_predicate) ->
  Lemma
  (requires has_local_crypto_predicate split_hpke_predicate_params hpke_pred.pred tagged_local_pred)
  (ensures has_hpke_predicate tagged_local_pred)
let intro_has_hpke_predicate #cusgs #hpke (tag, local_pred) =
  introduce
    forall tr usage plaintext info ad.
      fst usage = tag ==> hpke_pred.pred tr usage plaintext info ad == local_pred.pred tr usage plaintext info ad
  with (
    has_local_crypto_predicate_elim split_hpke_predicate_params hpke_pred.pred tag local_pred tr usage (plaintext, info, ad)
  )

(*** Global HPKE predicate builder ***)

val mk_hpke_predicate:
  {|crypto_usages|} ->
  list (string & hpke_crypto_predicate) ->
  hpke_crypto_predicate
let mk_hpke_predicate #cusgs l = {
  pred = mk_global_crypto_predicate split_hpke_predicate_params l;
  pred_later = (fun tr1 tr2 usage plaintext info ad -> mk_global_crypto_predicate_later split_hpke_predicate_params l tr1 tr2 usage (plaintext, info, ad));
}

val mk_hpke_predicate_correct:
  {|crypto_usages|} -> {|hpke_crypto_invariants|} ->
  tagged_local_preds:list (string & hpke_crypto_predicate) ->
  Lemma
  (requires
    hpke_pred == mk_hpke_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP has_hpke_predicate tagged_local_preds)
let mk_hpke_predicate_correct #cusgs #hpke tagged_local_preds =
  for_allP_eq has_hpke_predicate tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct split_hpke_predicate_params tagged_local_preds));
  FStar.Classical.forall_intro (FStar.Classical.move_requires intro_has_hpke_predicate)
