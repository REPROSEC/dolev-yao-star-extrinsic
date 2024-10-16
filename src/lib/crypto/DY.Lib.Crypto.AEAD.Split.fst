module DY.Lib.Crypto.AEAD.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_aead_predicate_params {|crypto_usages|}: split_crypto_predicate_parameters = {
  key_usage_t = key_usage:usage{AeadKey? key_usage};
  data_t = (bytes & bytes & bytes);
  get_usage = (fun key_usage ->
    let AeadKey tag _ = key_usage in
    tag
  );

  local_pred_t = aead_crypto_predicate;
  global_pred_t = trace -> key_usage:usage{AeadKey? key_usage} -> nonce:bytes -> msg:bytes -> ad:bytes -> prop;

  apply_local_pred = (fun pred (tr, key_usage, (nonce, msg, ad)) ->
    pred.pred tr key_usage nonce msg ad
  );
  apply_global_pred = (fun pred (tr, key_usage, (nonce, msg, ad)) ->
    pred tr key_usage nonce msg ad
  );
  mk_global_pred = (fun pred tr key_usage nonce msg ad ->
    pred (tr, key_usage, (nonce, msg, ad))
  );

  key_and_data_well_formed = (fun tr key_usage (nonce, msg, ad) ->
    bytes_well_formed tr nonce /\
    bytes_well_formed tr msg /\
    bytes_well_formed tr ad
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 key_usage (nonce, msg, ad) ->
    lpred.pred_later tr1 tr2 key_usage nonce msg ad
  );
}

val has_aead_predicate: {|crypto_invariants|} -> (string & aead_crypto_predicate) -> prop
let has_aead_predicate #cinvs (tag, local_pred) =
  forall (tr:trace) (key_usage:usage) (nonce:bytes) (msg:bytes) (ad:bytes).
    {:pattern aead_pred.pred tr key_usage nonce msg ad}
    match key_usage with
    | AeadKey aead_tag _ ->
        aead_tag = tag ==> aead_pred.pred tr key_usage nonce msg ad == local_pred.pred tr key_usage nonce msg ad
    | _ -> True

val intro_has_aead_predicate:
  {|crypto_invariants|} -> tagged_local_pred:(string & aead_crypto_predicate) ->
  Lemma
  (requires has_local_crypto_predicate split_aead_predicate_params aead_pred.pred tagged_local_pred)
  (ensures has_aead_predicate tagged_local_pred)
let intro_has_aead_predicate #cinvs (tag, local_pred) =
  introduce
    forall tr key_usage nonce msg ad.
      match key_usage with
      | AeadKey aead_tag _ ->
          aead_tag = tag ==> aead_pred.pred tr key_usage nonce msg ad == local_pred.pred tr key_usage nonce msg ad
      | _ -> True
  with (
    match key_usage with
    | AeadKey aead_tag _ ->
      has_local_crypto_predicate_elim split_aead_predicate_params aead_pred.pred tag local_pred tr key_usage (nonce, msg, ad)
    | _ -> ()
  )

(*** Global aead predicate builder ***)

val mk_aead_predicate:
  {|crypto_usages|} ->
  list (string & aead_crypto_predicate) ->
  aead_crypto_predicate
let mk_aead_predicate #cusgs l = {
  pred = mk_global_crypto_predicate split_aead_predicate_params l;
  pred_later = (fun tr1 tr2 key nonce msg ad -> mk_global_crypto_predicate_later split_aead_predicate_params l tr1 tr2 key (nonce, msg, ad));
}

val mk_aead_predicate_correct:
  {|crypto_invariants|} -> tagged_local_preds:list (string & aead_crypto_predicate) ->
  Lemma
  (requires
    aead_pred == mk_aead_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP has_aead_predicate tagged_local_preds)
let mk_aead_predicate_correct #cinvs tagged_local_preds =
  for_allP_eq has_aead_predicate tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct split_aead_predicate_params tagged_local_preds));
  FStar.Classical.forall_intro (FStar.Classical.move_requires intro_has_aead_predicate)
