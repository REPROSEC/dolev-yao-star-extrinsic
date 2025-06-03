module DY.Lib.Crypto.MAC.Split

open FStar.List.Tot { for_allP, for_allP_eq }
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_mac_predicate_params {|crypto_usages|}: split_crypto_predicate_parameters = {
  key_usage_t = key_usg:usage{MacKey? key_usg};
  data_t = (bytes & bytes);
  get_usage = (fun key_usg ->
    let MacKey tag _ = key_usg in
    tag
  );

  local_pred_t = mac_crypto_predicate;
  global_pred_t = tr:trace -> key_usg:usage{MacKey? key_usg} -> key:bytes -> msg:bytes -> prop;

  apply_local_pred = (fun pred (tr, key_usg, (key, msg)) ->
    pred.pred tr key_usg key msg
  );
  apply_global_pred = (fun pred (tr, key_usg, (key, msg)) ->
    pred tr key_usg key msg
  );
  mk_global_pred = (fun pred tr key_usg key msg ->
    pred (tr, key_usg, (key, msg))
  );

  data_well_formed = (fun tr (key, msg) ->
    bytes_well_formed tr key /\
    bytes_well_formed tr msg
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 key_usg (key, msg) ->
    lpred.pred_later tr1 tr2 key_usg key msg
  );
}

val has_mac_predicate: {|crypto_invariants|} -> (string & mac_crypto_predicate) -> prop
let has_mac_predicate #cinvs (tag, local_pred) =
  forall (tr:trace) (key_usg:usage) (key:bytes) (msg:bytes).
    {:pattern mac_pred.pred tr key_usg key msg}
    match key_usg with
    | MacKey mac_tag _ ->
        mac_tag = tag ==> mac_pred.pred tr key_usg key msg == local_pred.pred tr key_usg key msg
    | _ -> True

val intro_has_mac_predicate:
  {|crypto_invariants|} -> tagged_local_pred:(string & mac_crypto_predicate) ->
  Lemma
  (requires has_local_crypto_predicate split_mac_predicate_params mac_pred.pred tagged_local_pred)
  (ensures has_mac_predicate tagged_local_pred)
let intro_has_mac_predicate #cinvs (tag, local_pred) =
  introduce
    forall tr key_usg key msg.
      match key_usg with
      | MacKey mac_tag _ ->
          mac_tag = tag ==> mac_pred.pred tr key_usg key msg == local_pred.pred tr key_usg key msg
      | _ -> True
  with (
    match key_usg with
    | MacKey mac_tag _ ->
      has_local_crypto_predicate_elim (split_mac_predicate_params) mac_pred.pred tag local_pred tr key_usg (key, msg)
    | _ -> ()
  )

(*** Global mac predicate builder ***)

val mk_mac_predicate:
  {|crypto_usages|} ->
  list (string & mac_crypto_predicate) ->
  mac_crypto_predicate
let mk_mac_predicate #cusgs l = {
  pred = mk_global_crypto_predicate split_mac_predicate_params l;
  pred_later = (fun tr1 tr2 key_usg key msg ->
    mk_global_crypto_predicate_later split_mac_predicate_params l tr1 tr2 key_usg (key, msg)
  );
}

val mk_mac_predicate_correct:
  {|crypto_invariants|} -> tagged_local_preds:list (string & mac_crypto_predicate) ->
  Lemma
  (requires
    mac_pred == mk_mac_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP has_mac_predicate tagged_local_preds)
let mk_mac_predicate_correct #cinvs tagged_local_preds =
  for_allP_eq has_mac_predicate tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct split_mac_predicate_params tagged_local_preds));
  FStar.Classical.forall_intro (FStar.Classical.move_requires intro_has_mac_predicate)
