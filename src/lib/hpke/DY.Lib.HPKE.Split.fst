module DY.Lib.HPKE.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate
open DY.Lib.HPKE.Lemmas

let split_hpke_predicate_params {|crypto_usages|}: split_crypto_predicate_parameters = {
  key_t = bytes;
  key_usage_t = (string & bytes);
  data_t = bytes & bytes & bytes;
  get_usage = (fun (usage_tag, usage_data) ->
    usage_tag
  );

  key_well_formed = bytes_well_formed;
  has_usage_split = (fun tr key hpke_usage ->
    has_hpke_sk_usage tr key (mk_hpke_sk_usage hpke_usage)
  );
  has_usage_split_later = (fun tr1 tr2 key hpke_usage ->
    normalize_term_spec bytes_well_formed;
    get_usage_later tr1 tr2 key
  );

  local_pred_t = hpke_crypto_predicate;
  global_pred_t = tr:trace -> usage:(string & bytes) -> key:bytes{key `has_hpke_sk_usage tr` (mk_hpke_sk_usage usage)} -> plaintext:bytes -> info:bytes -> ad:bytes -> prop;

  apply_local_pred = (fun pred (|tr, usage, key, (plaintext, info, ad)|) ->
    key `has_hpke_sk_usage tr` (mk_hpke_sk_usage usage) /\
    pred.pred tr usage key plaintext info ad
  );
  apply_global_pred = (fun pred (|tr, usage, key, (plaintext, info, ad)|) ->
    key `has_hpke_sk_usage tr` (mk_hpke_sk_usage usage) /\
    pred tr usage key plaintext info ad
  );
  mk_global_pred = (fun pred tr usage key plaintext info ad ->
    key `has_hpke_sk_usage tr` (mk_hpke_sk_usage usage) /\
    pred (|tr, usage, key, (plaintext, info, ad)|)
  );

  data_well_formed = (fun tr (plaintext, info, ad) ->
    bytes_well_formed tr plaintext /\
    bytes_well_formed tr info /\
    bytes_well_formed tr ad
  );

  apply_mk_global_pred = (fun bare x -> admit());
  apply_local_pred_later = (fun lpred tr1 tr2 usage key (plaintext, info, ad) ->
    lpred.pred_later tr1 tr2 usage key plaintext info ad
  );
}

val has_hpke_predicate: {|crypto_usages|} -> {|hpke_crypto_invariants|} -> (string & hpke_crypto_predicate) -> prop
let has_hpke_predicate #cusgs #hpke (tag, local_pred) =
  forall (tr:trace) (usage:(string & bytes)) (key:bytes{key `has_hpke_sk_usage tr` (mk_hpke_sk_usage usage)}) (plaintext:bytes) (info:bytes) (ad:bytes).
    {:pattern hpke_pred.pred tr usage key plaintext info ad}
    fst usage = tag ==> hpke_pred.pred tr usage key plaintext info ad == local_pred.pred tr usage key plaintext info ad

val intro_has_hpke_predicate:
  {|crypto_usages|} -> {|hpke_crypto_invariants|} ->
  tagged_local_pred:(string & hpke_crypto_predicate) ->
  Lemma
  (requires has_local_crypto_predicate split_hpke_predicate_params hpke_pred.pred tagged_local_pred)
  (ensures has_hpke_predicate tagged_local_pred)
let intro_has_hpke_predicate #cusgs #hpke (tag, local_pred) =
  introduce
    forall tr usage (key:bytes{key `has_hpke_sk_usage tr` (mk_hpke_sk_usage usage)}) plaintext info ad.
      fst usage = tag ==> hpke_pred.pred tr usage key plaintext info ad == local_pred.pred tr usage key plaintext info ad
  with (
    has_local_crypto_predicate_elim split_hpke_predicate_params hpke_pred.pred tag local_pred tr usage key (plaintext, info, ad);
    assume(has_hpke_predicate (tag, local_pred))
  )

(*** Global HPKE predicate builder ***)

val mk_hpke_predicate:
  {|crypto_usages|} ->
  list (string & hpke_crypto_predicate) ->
  hpke_crypto_predicate
let mk_hpke_predicate #cusgs l = {
  pred = (fun tr usage key plaintext info ad -> mk_global_crypto_predicate split_hpke_predicate_params l tr usage key plaintext info ad);
  pred_later = (fun tr1 tr2 usage key plaintext info ad -> mk_global_crypto_predicate_later split_hpke_predicate_params l tr1 tr2 usage key (plaintext, info, ad));
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
