module DY.Lib.Crypto.PkEncryption.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.Crypto.SplitPredicate

let split_pkenc_predicate_params {|crypto_usages|}: split_crypto_predicate_parameters = {
  key_usage_t = sk_usage:usage{PkeKey? sk_usage};
  data_t = bytes;
  get_usage = (fun sk_usage ->
    let PkeKey tag _ = sk_usage in
    tag
  );

  local_pred_t = pkenc_crypto_predicate;
  global_pred_t = tr:trace -> sk_usage:usage{PkeKey? sk_usage} -> msg:bytes -> prop;

  apply_local_pred = (fun pred (tr, sk_usage, msg) ->
    pred.pred tr sk_usage msg
  );
  apply_global_pred = (fun pred (tr, sk_usage, msg) ->
    pred tr sk_usage msg
  );
  mk_global_pred = (fun pred tr sk_usage msg ->
    pred (tr, sk_usage, msg)
  );

  data_well_formed = (fun tr msg ->
    bytes_well_formed tr msg
  );

  apply_mk_global_pred = (fun bare x -> ());
  apply_local_pred_later = (fun lpred tr1 tr2 sk_usage msg ->
    lpred.pred_later tr1 tr2 sk_usage msg
  );
}

val has_pkenc_predicate: {|crypto_invariants|} -> (string & pkenc_crypto_predicate) -> prop
let has_pkenc_predicate #cinvs (tag, local_pred) =
  forall (tr:trace) (sk_usage:usage) (msg:bytes).
    {:pattern pkenc_pred.pred tr sk_usage msg}
    match sk_usage with
    | PkeKey pkenc_tag _ ->
        pkenc_tag = tag ==> pkenc_pred.pred tr sk_usage msg == local_pred.pred tr sk_usage msg
    | _ -> True

val intro_has_pkenc_predicate:
  {|crypto_invariants|} -> tagged_local_pred:(string & pkenc_crypto_predicate) ->
  Lemma
  (requires has_local_crypto_predicate split_pkenc_predicate_params pkenc_pred.pred tagged_local_pred)
  (ensures has_pkenc_predicate tagged_local_pred)
let intro_has_pkenc_predicate #cinvs (tag, local_pred) =
  introduce
    forall tr sk_usage msg.
      match sk_usage with
      | PkeKey pkenc_tag _ ->
          pkenc_tag = tag ==> pkenc_pred.pred tr sk_usage msg == local_pred.pred tr sk_usage msg
      | _ -> True
  with (
    match sk_usage with
    | PkeKey pkenc_tag _ ->
      has_local_crypto_predicate_elim split_pkenc_predicate_params pkenc_pred.pred tag local_pred tr sk_usage msg
    | _ -> ()
  )

(*** Global pkenc predicate builder ***)

val mk_pkenc_predicate:
  {|crypto_usages|} ->
  list (string & pkenc_crypto_predicate) ->
  pkenc_crypto_predicate
let mk_pkenc_predicate #cusgs l = {
  pred = mk_global_crypto_predicate split_pkenc_predicate_params l;
  pred_later = mk_global_crypto_predicate_later split_pkenc_predicate_params l;
}

val mk_pkenc_predicate_correct:
  {|crypto_invariants|} -> tagged_local_preds:list (string & pkenc_crypto_predicate) ->
  Lemma
  (requires
    pkenc_pred == mk_pkenc_predicate tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP has_pkenc_predicate tagged_local_preds)
let mk_pkenc_predicate_correct #cinvs tagged_local_preds =
  for_allP_eq has_pkenc_predicate tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_crypto_predicate_correct split_pkenc_predicate_params tagged_local_preds));
  FStar.Classical.forall_intro (FStar.Classical.move_requires intro_has_pkenc_predicate)
