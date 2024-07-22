module DY.Lib.Crypto.KdfExpand.Split

open Comparse // for_allP, for_allP_eq
open DY.Core
open DY.Lib.SplitFunction

let split_kdf_expand_usage_get_usage_params = {
  singleton_split_function_parameters string with

  tagged_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & bytes;
  raw_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & bytes;
  output_t = usage;

  decode_tagged_data = (fun (prk_usage, info) ->
    let KdfExpandKey tag _ = prk_usage in
    Some (tag, (prk_usage, info))
  );

  local_fun_t = kdf_expand_crypto_usage;
  global_fun_t = prk_usage:usage{KdfExpandKey? prk_usage} -> info:bytes -> usage;

  default_global_fun = (fun prk_usage info -> NoUsage);

  apply_local_fun = (fun lfun (prk_usage, info) ->
    lfun.get_usage prk_usage info
  );
  apply_global_fun = (fun gfun (prk_usage, info) ->
    gfun prk_usage info
  );
  mk_global_fun = (fun gfun prk_usage info ->
    gfun (prk_usage, info)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

let split_kdf_expand_usage_get_label_params = {
  singleton_split_function_parameters string with

  tagged_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & label & bytes;
  raw_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & label & bytes;
  output_t = label;

  decode_tagged_data = (fun (prk_usage, prk_label, info) ->
    let KdfExpandKey tag _ = prk_usage in
    Some (tag, (prk_usage, prk_label, info))
  );

  local_fun_t = kdf_expand_crypto_usage;
  global_fun_t = prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label -> info:bytes -> label;

  default_global_fun = (fun prk_usage prk_label info -> prk_label);

  apply_local_fun = (fun lfun (prk_usage, prk_label, info) ->
    lfun.get_label prk_usage prk_label info
  );
  apply_global_fun = (fun gfun (prk_usage, prk_label, info) ->
    gfun prk_usage prk_label info
  );
  mk_global_fun = (fun gfun prk_usage prk_label info ->
    gfun (prk_usage, prk_label, info)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

val has_kdf_expand_usage: cusgs:crypto_usages -> (string & kdf_expand_crypto_usage) -> prop
let has_kdf_expand_usage cinvs (tag, crypto_usage) =
  has_local_fun split_kdf_expand_usage_get_usage_params kdf_expand_usage.get_usage (tag, crypto_usage) /\
  has_local_fun split_kdf_expand_usage_get_label_params kdf_expand_usage.get_label (tag, crypto_usage)

(*** Global kdf_expand usage builder ***)

val mk_global_kdf_expand_usage_get_usage:
  list (string & kdf_expand_crypto_usage) ->
  prk_usage:usage{KdfExpandKey? prk_usage} -> info:bytes ->
  usage
let mk_global_kdf_expand_usage_get_usage l =
  mk_global_fun (split_kdf_expand_usage_get_usage_params) l

val mk_global_kdf_expand_usage_get_label:
  list (string & kdf_expand_crypto_usage) ->
  prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label -> info:bytes ->
  label
let mk_global_kdf_expand_usage_get_label l =
  mk_global_fun (split_kdf_expand_usage_get_label_params) l

val mk_global_kdf_expand_usage_correct:
  cusgs:crypto_usages -> lusages:list (string & kdf_expand_crypto_usage) ->
  Lemma
  (requires
    kdf_expand_usage.get_usage == mk_global_kdf_expand_usage_get_usage lusages /\
    kdf_expand_usage.get_label == mk_global_kdf_expand_usage_get_label lusages /\
    List.Tot.no_repeats_p (List.Tot.map fst lusages)
  )
  (ensures for_allP (has_kdf_expand_usage cusgs) lusages)
let mk_global_kdf_expand_usage_correct cusgs lusages =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst lusages);
  for_allP_eq (has_kdf_expand_usage cusgs) lusages;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_kdf_expand_usage_get_usage_params lusages));
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_kdf_expand_usage_get_label_params lusages))

val mk_global_kdf_expand_usage_get_label_lemma:
  lusages:list (string & kdf_expand_crypto_usage) ->
  tr:trace ->
  prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label -> info:bytes ->
  Lemma ((mk_global_kdf_expand_usage_get_label lusages prk_usage prk_label info) `can_flow tr` prk_label)
let mk_global_kdf_expand_usage_get_label_lemma lusages tr prk_usage prk_label info =
  mk_global_fun_eq split_kdf_expand_usage_get_label_params lusages (prk_usage, prk_label, info);
  introduce forall lusages. split_kdf_expand_usage_get_label_params.apply_local_fun lusages (prk_usage, prk_label, info) `can_flow tr` prk_label with (
    lusages.get_label_lemma tr prk_usage prk_label info
  )

val mk_kdf_expand_usage: list (string & kdf_expand_crypto_usage) -> kdf_expand_crypto_usage
let mk_kdf_expand_usage lusages = {
  get_usage = mk_global_kdf_expand_usage_get_usage lusages;
  get_label = mk_global_kdf_expand_usage_get_label lusages;
  get_label_lemma = mk_global_kdf_expand_usage_get_label_lemma lusages;
}
