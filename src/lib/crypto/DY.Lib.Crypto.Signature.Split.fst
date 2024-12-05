module DY.Lib.Crypto.Signature.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_sign_predicate_params {|crypto_usages|}: split_crypto_predicate_parameters = {
  key_t = bytes;
  key_usage_t = sk_usage:usage{SigKey? sk_usage};
  data_t = (bytes & bytes);
  get_usage = (fun vk_usg ->
    let SigKey tag _ = vk_usg in
    tag
  );

  key_well_formed = bytes_well_formed;
  has_usage_split = has_signkey_usage;
  has_usage_split_later = (fun tr1 tr2 vk sk_usage ->
    normalize_term_spec bytes_well_formed;
    match vk with
    | Vk sk -> (
      get_usage_later tr1 tr2 sk
    )
    | _ -> ()
  );

  local_pred_t = sign_crypto_predicate;
  global_pred_t = tr:trace -> sk_usage:usage{SigKey? sk_usage} -> vk:bytes{vk `has_signkey_usage tr` sk_usage} -> msg:bytes -> prop;

  apply_local_pred = (fun pred (|tr, sk_usage, sk, msg|) ->
    pred.pred tr sk_usage sk msg
  );
  apply_global_pred = (fun pred (|tr, sk_usage, sk, msg|) ->
    pred tr sk_usage sk msg
  );
  mk_global_pred = (fun pred tr sk_usage sk msg ->
    pred (|tr, sk_usage, sk, msg|)
  );

  data_well_formed = (fun tr (vk, msg) ->
    bytes_well_formed tr vk /\
    bytes_well_formed tr msg
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 sk_usage (vk, msg) ->
    lpred.pred_later tr1 tr2 sk_usage vk msg
  );
}

val has_sign_predicate: {|crypto_invariants|} -> (string & sign_crypto_predicate) -> prop
let has_sign_predicate #cinvs (tag, local_pred) =
  forall (tr:trace) (sk_usage:usage) (vk:bytes{vk `has_signkey_usage tr` sk_usage}) (msg:bytes).
    {:pattern sign_pred.pred tr sk_usage vk msg}
    match sk_usage with
    | SigKey sign_tag _ ->
        sign_tag = tag ==> sign_pred.pred tr sk_usage vk msg == local_pred.pred tr sk_usage vk msg
    | _ -> True

val intro_has_sign_predicate:
  {|crypto_invariants|} -> tagged_local_pred:(string & sign_crypto_predicate) ->
  Lemma
  (requires has_local_crypto_predicate split_sign_predicate_params sign_pred.pred tagged_local_pred)
  (ensures has_sign_predicate tagged_local_pred)
let intro_has_sign_predicate #cinvs (tag, local_pred) =
  introduce
    forall tr sk_usage vk msg.
      match sk_usage with
      | SigKey sign_tag _ ->
          sign_tag = tag ==> sign_pred.pred tr sk_usage vk msg == local_pred.pred tr sk_usage vk msg
      | _ -> True
  with (
    match sk_usage with
    | SigKey sign_tag _ ->
      has_local_crypto_predicate_elim (split_sign_predicate_params) sign_pred.pred tag local_pred tr sk_usage vk msg
    | _ -> ()
  )

(*** Global sign predicate builder ***)

val mk_sign_predicate:
  {|crypto_usages|} ->
  list (string & sign_crypto_predicate) ->
  sign_crypto_predicate
let mk_sign_predicate #cusgs l = {
  pred = mk_global_crypto_predicate split_sign_predicate_params l;
  pred_later = (fun tr1 tr2 sk_usage vk msg ->
    mk_global_crypto_predicate_later split_sign_predicate_params l tr1 tr2 sk_usage vk msg
  );
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
