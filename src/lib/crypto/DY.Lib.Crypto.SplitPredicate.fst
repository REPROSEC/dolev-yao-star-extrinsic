module DY.Lib.Crypto.SplitPredicate

open DY.Core
open DY.Lib.SplitFunction

/// This module defines a library to create a global cryptographic predicate from several independent local predicates.
/// This is based on the DY.Lib.SplitFunction module,
/// and is specific to cryptographic predicates that follow a specific shape,
/// where the tag is a string derived from the usage of the key,
/// and the predicate stays true when the trace grows.
/// For these specific cryptographic predicates, this module allows to define predicate splitting with little boilerplate.

noeq
type split_crypto_predicate_parameters = {
  key_usage_t: Type;
  data_t: Type;
  get_usage: key_usage_t -> string;

  local_pred_t: Type;
  global_pred_t: Type;

  apply_local_pred: local_pred_t -> (trace & key_usage_t & data_t) -> prop;
  apply_global_pred: global_pred_t -> (trace & key_usage_t & data_t) -> prop;
  mk_global_pred: ((trace & key_usage_t & data_t) -> prop) -> global_pred_t;

  key_and_data_well_formed: trace -> key_usage_t -> data_t -> prop;

  apply_mk_global_pred: bare:((trace & key_usage_t & data_t) -> prop) -> x:(trace & key_usage_t & data_t) -> Lemma
    (apply_global_pred (mk_global_pred bare) x == bare x);
  apply_local_pred_later:
    lpred: local_pred_t ->
    tr1:trace -> tr2:trace ->
    key:key_usage_t -> data:data_t ->
    Lemma
    (requires
      apply_local_pred lpred (tr1, key, data) /\
      key_and_data_well_formed tr1 key data /\
      tr1 <$ tr2)
    (ensures apply_local_pred lpred (tr2, key, data))
  ;
}

val always_false: #a:Type -> a -> prop
let always_false #a x = False

let split_crypto_predicate_parameters_to_split_function_parameters (params:split_crypto_predicate_parameters): split_function_parameters = {
  singleton_split_function_parameters string with

  tagged_data_t = (trace & params.key_usage_t & params.data_t);
  raw_data_t = (trace & params.key_usage_t & params.data_t);
  output_t = prop;

  decode_tagged_data = (fun (tr, key, data) ->
    let tag = params.get_usage key in
    Some (tag, (tr, key, data))
  );

  local_fun_t = mk_dependent_type params.local_pred_t;
  global_fun_t = params.global_pred_t;

  default_global_fun = params.mk_global_pred always_false;

  apply_local_fun = (fun #tag_set -> params.apply_local_pred);
  apply_global_fun = params.apply_global_pred;
  mk_global_fun = params.mk_global_pred;
  apply_mk_global_fun = params.apply_mk_global_pred;
}

val has_local_crypto_predicate:
  params:split_crypto_predicate_parameters ->
  params.global_pred_t -> (string & params.local_pred_t) ->
  prop
let has_local_crypto_predicate params global_pred (tag, local_pred) =
  has_local_fun (split_crypto_predicate_parameters_to_split_function_parameters params) global_pred (|tag, local_pred|)

val has_local_crypto_predicate_elim:
  params:split_crypto_predicate_parameters ->
  global_pred:params.global_pred_t -> tag:string -> local_pred:params.local_pred_t ->
  tr:trace -> key:params.key_usage_t -> data:params.data_t ->
  Lemma
  (requires has_local_crypto_predicate params global_pred (tag, local_pred))
  (ensures
    params.get_usage key == tag ==> (params.apply_global_pred global_pred (tr, key, data) == params.apply_local_pred local_pred (tr, key, data))
  )
let has_local_crypto_predicate_elim params global_pred tag local_pred tr key data =
  has_local_fun_elim (split_crypto_predicate_parameters_to_split_function_parameters params) global_pred tag local_pred (tr, key, data)

val mk_global_crypto_predicate:
  params:split_crypto_predicate_parameters ->
  list (string & params.local_pred_t) ->
  params.global_pred_t
let mk_global_crypto_predicate params tagged_local_preds =
  mk_global_fun (split_crypto_predicate_parameters_to_split_function_parameters params) (mk_dependent_tagged_local_funs tagged_local_preds)

val mk_global_crypto_predicate_later:
  params:split_crypto_predicate_parameters ->
  tagged_local_preds:list (string & params.local_pred_t) ->
  tr1:trace -> tr2:trace ->
  key:params.key_usage_t -> data:params.data_t ->
  Lemma
  (requires
    params.apply_global_pred (mk_global_crypto_predicate params tagged_local_preds) (tr1, key, data) /\
    params.key_and_data_well_formed tr1 key data /\
    tr1 <$ tr2
  )
  (ensures params.apply_global_pred (mk_global_crypto_predicate params tagged_local_preds) (tr2, key, data))
let mk_global_crypto_predicate_later params tagged_local_preds tr1 tr2 key data =
  let fparams = split_crypto_predicate_parameters_to_split_function_parameters params in
  params.apply_mk_global_pred always_false (tr1, key, data);
  mk_global_fun_eq fparams (mk_dependent_tagged_local_funs tagged_local_preds) (tr1, key, data);
  mk_global_fun_eq fparams (mk_dependent_tagged_local_funs tagged_local_preds) (tr2, key, data);
  introduce forall tag_set lpred. fparams.apply_local_fun lpred (tr1, key, data) ==> fparams.apply_local_fun #tag_set lpred (tr2, key, data) with (
    introduce _ ==> _ with _. params.apply_local_pred_later lpred tr1 tr2 key data
  )

val mk_global_crypto_predicate_correct:
  params:split_crypto_predicate_parameters ->
  tagged_local_preds:list (string & params.local_pred_t) ->
  tag:string -> local_pred:params.local_pred_t ->
  Lemma
  (requires
    FStar.List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds) /\
    List.Tot.memP (tag, local_pred) tagged_local_preds
  )
  (ensures has_local_crypto_predicate params (mk_global_crypto_predicate params tagged_local_preds) (tag, local_pred))
let mk_global_crypto_predicate_correct params tagged_local_preds tag local_pred =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst tagged_local_preds);
  map_dfst_mk_dependent_tagged_local_funs tagged_local_preds;
  memP_mk_dependent_tagged_local_funs tagged_local_preds tag local_pred;
  mk_global_fun_correct (split_crypto_predicate_parameters_to_split_function_parameters params) (mk_dependent_tagged_local_funs tagged_local_preds) tag local_pred
