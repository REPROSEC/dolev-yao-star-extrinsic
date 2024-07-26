module DY.Lib.SplitFunction

open FStar.List.Tot
open Comparse //for_allP, for_allP_eq

#set-options "--fuel 1 --ifuel 1"

/// This module defines a library to create a global function from several independent local functions,
/// also called the "split function methodology".
///
/// DY* proofs rely on global protocol invariants composed of functions and predicates
/// (e.g. what protocol participants are allowed to store, are allowed to sign, or how a usage evolves throughs KDFs),
/// that must be preserved by each step of the protocol.
/// The practice of defining this global protocol invariant monolithically somewhere has a few drawbacks:
/// - it does not allows the user to do modular proofs,
///   as many unrelated functions and predicates are put in the same place
/// - when modifying the global invariants for some sub-component,
///   other unrelated sub-components will need to be re-checked
///   (because the local invariant they depend on has changed)
///   (and their proof might fail if the SMT gods are angry!)
/// - it makes it difficult to create reusable components
///   (such as a generic state to store private keys)
///
/// With this module, we can create a global function from several independent local functions (see mk_global_fun).
/// Then, proofs of theorems will take as parameter some global function,
/// with the precondition that it contains a specific local function (see has_local_fun).
/// In this way, proofs will work for any global function
/// as long as it contains the relevant local function.
/// (This is in contrast to proofs reyling on
/// a monolithic global function
/// that is defined at the top of a file (using val and let).)
///
/// This solves all the problems mentioned above:
/// functions are defined (locally) where they belong,
/// proofs are modular because they only depend on
/// the relevant local function being contained in the global function
/// (a property that is not affected by other unrelated local functions).
///
/// Under the hood, the split function methodology
/// is simply factorizing out a common pattern we see
/// when writing monolithic global functions.
/// Indeed, such a monolithic global function usually
/// - first disambiguate to which local function its input belong to
/// - then dispatch the input to that local function, maybe after some modifications.
///
/// In practice, the global function is structured like this:
/// let global_function param1 param2 param3 ... =
///   // First detect in which sub-component we are in
///   let tag = ... in
///   // then dispatch to the corresponding local function
///   if tag `belong_to` tag_set_1 then
///     local_fun_1 ...
///   else if tag `belong_to` tag_set_2 then
///     local_fun_2 ...
///   ...
///   else
///     default_fun ...
///
/// The tag may be obtained in different ways,
/// for example with the key usage (e.g. for a signature function, see DY.Core.Bytes.Type.usage),
/// or because some messages are tagged
/// (e.g. the state content in a state function or the signature input in signature function).
/// How to obtain this tag is not always trivial,
/// it is actually a core argument in the proof of
/// why it is secure to deploy different sub-components in parallel.
///
/// The split function methodology can be used to implement horizontal composition:
/// as long as we can find a way to disambiguate the composed protocols (using the tag),
/// we can easily construct a global function implementing this horizontal composition.

/// The parameters of the split function methodology.

noeq type split_function_parameters = {
  // Functions to model set of tags
  tag_set_t: Type;
  tag_t: Type;
  is_disjoint: tag_set_t -> tag_set_t -> prop;
  tag_belong_to: tag_t -> tag_set_t -> bool;
  cant_belong_to_disjoint_sets:
    tag:tag_t -> tag_set_1:tag_set_t -> tag_set_2:tag_set_t -> Lemma
    (~(tag_set_1 `is_disjoint` tag_set_2 /\ tag `tag_belong_to` tag_set_1 /\ tag `tag_belong_to` tag_set_2));

  // Input type for the global function
  tagged_data_t: Type;

  // Input type for the local functions
  raw_data_t: Type;

  // Output type for the local and global functions
  output_t: Type;

  // We can decode the global function input
  // into a tag and a local function input
  decode_tagged_data: tagged_data_t -> option (tag_t & raw_data_t);

  // Types for the local functions and the global function
  local_fun_t: Type;
  global_fun_t: Type;

  default_global_fun: global_fun_t;

  // Apply a local function to its input
  apply_local_fun: local_fun_t -> raw_data_t -> output_t;
  // Apply the global function to its input
  apply_global_fun: global_fun_t -> tagged_data_t -> output_t;
  // Create a global function
  mk_global_fun: (tagged_data_t -> output_t) -> global_fun_t;
  // Correctness theorem on creating and applying a global function
  apply_mk_global_fun: bare:(tagged_data_t -> output_t) -> x:tagged_data_t -> Lemma
    (apply_global_fun (mk_global_fun bare) x == bare x);
}

/// Do a global function contain some given local function with some set of tags?
/// This will be a crucial precondition for the correctness theorem `local_eq_global_lemma`.

val has_local_fun: params:split_function_parameters -> params.global_fun_t -> (params.tag_set_t & params.local_fun_t) -> prop
let has_local_fun params global_fun (tag_set, local_fun) =
  forall tagged_data.
    match params.decode_tagged_data tagged_data with
    | Some (tag, raw_data) ->
      tag `params.tag_belong_to` tag_set ==> (params.apply_global_fun global_fun tagged_data == params.apply_local_fun local_fun raw_data)
    | None -> True

/// A lemma that may be useful when the `forall` quantification doesn't trigger well

val has_local_fun_elim:
  params:split_function_parameters ->
  global_fun:params.global_fun_t -> tag_set:params.tag_set_t -> local_fun:params.local_fun_t ->
  tagged_data:params.tagged_data_t ->
  Lemma
  (requires has_local_fun params global_fun (tag_set, local_fun))
  (ensures (
    match params.decode_tagged_data tagged_data with
    | Some (tag, raw_data) ->
      tag `params.tag_belong_to` tag_set ==> (params.apply_global_fun global_fun tagged_data == params.apply_local_fun local_fun raw_data)
    | None -> True
  ))
let has_local_fun_elim params global_fun tag_set local_fun tagged_data = ()

/// Returns the first local function associated with a tag set containing `tag`, if it exists.
/// In practice, only one tag set may contain `tag` because tag sets are mutually disjoint
/// (c.f. precondition of `mk_global_fun_correct`).
/// In that case, this function returns the *unique* local function associated with a tag set containing `tag`.
val find_local_fun: params:split_function_parameters -> list (params.tag_set_t & params.local_fun_t) -> params.tag_t -> option params.local_fun_t
let rec find_local_fun params tagged_local_funs tag =
  match tagged_local_funs with
  | [] -> None
  | (h_tag_set, h_local_fun)::t_tagged_local_funs -> (
    if tag `params.tag_belong_to` h_tag_set then
      Some h_local_fun
    else
      find_local_fun params t_tagged_local_funs tag
  )

val mk_global_fun_aux: params:split_function_parameters -> list (params.tag_set_t & params.local_fun_t) -> params.tagged_data_t -> params.output_t
let mk_global_fun_aux params tagged_local_funs tagged_data =
  match params.decode_tagged_data tagged_data with
  | Some (tag_set, raw_data) -> (
    match find_local_fun params tagged_local_funs tag_set with
    | Some tagged_local_fun -> params.apply_local_fun tagged_local_fun raw_data
    | None -> params.apply_global_fun params.default_global_fun tagged_data
  )
  | None -> params.apply_global_fun params.default_global_fun tagged_data

/// Given a list of tags and local functions, create the global function.

[@@"opaque_to_smt"]
val mk_global_fun: params:split_function_parameters -> list (params.tag_set_t & params.local_fun_t) -> params.global_fun_t
let mk_global_fun params tagged_local_funs =
  params.mk_global_fun (mk_global_fun_aux params tagged_local_funs)

val memP_map:
  #a:Type -> #b:Type ->
  f:(a -> b) -> l:list a -> x:a ->
  Lemma
  (requires List.Tot.memP x l)
  (ensures List.Tot.memP (f x) (List.Tot.map f l))
let rec memP_map #a #b f l x =
  match l with
  | [] -> ()
  | h::t ->
    introduce x =!= h ==> List.Tot.memP (f x) (List.Tot.map f t)
    with _. memP_map f t x

val for_all_pairsP : #a:Type -> (a -> a -> prop) -> list a -> prop
let rec for_all_pairsP #a disj l =
  match l with
  | [] -> True
  | h::t -> (for_allP (disj h) t) /\ for_all_pairsP disj t

val mk_global_fun_correct_aux:
  params:split_function_parameters -> tagged_local_funs:list (params.tag_set_t & params.local_fun_t) -> tag_set:params.tag_set_t -> local_fun:params.local_fun_t -> tag:params.tag_t ->
  Lemma
  (requires
    for_all_pairsP (params.is_disjoint) (List.Tot.map fst tagged_local_funs) /\
    tag `params.tag_belong_to` tag_set /\
    List.Tot.memP (tag_set, local_fun) tagged_local_funs
  )
  (ensures find_local_fun params tagged_local_funs tag == Some local_fun)
let rec mk_global_fun_correct_aux params tagged_local_funs tag_set tagged_local_fun tag =
  match tagged_local_funs with
  | [] -> ()
  | (h_tag_set, h_tagged_local_fun)::t_tagged_local_funs -> (
    if tag `params.tag_belong_to` h_tag_set then (
      introduce (List.Tot.memP (tag_set, tagged_local_fun) t_tagged_local_funs) ==> False with _. (
        for_allP_eq (params.is_disjoint h_tag_set) (List.Tot.map fst t_tagged_local_funs);
        memP_map fst t_tagged_local_funs (tag_set, tagged_local_fun);
        params.cant_belong_to_disjoint_sets tag h_tag_set tag_set
      )
    ) else (
      mk_global_fun_correct_aux params t_tagged_local_funs tag_set tagged_local_fun tag
    )
  )

val mk_global_fun_correct:
  params:split_function_parameters -> tagged_local_funs:list (params.tag_set_t & params.local_fun_t) -> tag_set:params.tag_set_t -> local_fun:params.local_fun_t ->
  Lemma
  (requires
    for_all_pairsP (params.is_disjoint) (List.Tot.map fst tagged_local_funs) /\
    List.Tot.memP (tag_set, local_fun) tagged_local_funs
  )
  (ensures has_local_fun params (mk_global_fun params tagged_local_funs) (tag_set, local_fun))
let mk_global_fun_correct params tagged_local_funs tag_set local_fun =
  reveal_opaque (`%mk_global_fun) (mk_global_fun);
  introduce
    forall tagged_data.
      match params.decode_tagged_data tagged_data with
      | Some (tag, raw_data) ->
        tag `params.tag_belong_to` tag_set ==> (params.apply_global_fun (mk_global_fun params tagged_local_funs) tagged_data == params.apply_local_fun local_fun raw_data)
      | None -> True
  with (
    match params.decode_tagged_data tagged_data with
    | Some (tag, raw_data) -> (
      if tag `params.tag_belong_to` tag_set then (
        mk_global_fun_correct_aux params tagged_local_funs tag_set local_fun tag;
        params.apply_mk_global_fun (mk_global_fun_aux params tagged_local_funs) tagged_data
      ) else ()
    )
    | None -> ()
  )

/// Equivalence theorem for `mk_global_fun`.
/// This may be useful to lift properties of the local functions
/// to property on the global function.
/// (e.g. the function keep the same output when the trace grows.)

val mk_global_fun_eq:
  params:split_function_parameters -> tagged_local_funs:list (params.tag_set_t & params.local_fun_t) ->
  tagged_data:params.tagged_data_t ->
  Lemma (
    params.apply_global_fun (mk_global_fun params tagged_local_funs) tagged_data == (
      match params.decode_tagged_data tagged_data with
      | Some (tag, raw_data) -> (
        match find_local_fun params tagged_local_funs tag with
        | Some tagged_local_fun -> params.apply_local_fun tagged_local_fun raw_data
        | None -> params.apply_global_fun params.default_global_fun tagged_data
      )
      | None -> params.apply_global_fun params.default_global_fun tagged_data
    )
  )
let mk_global_fun_eq params tagged_local_funs tagged_data =
  reveal_opaque (`%mk_global_fun) (mk_global_fun);
  params.apply_mk_global_fun (mk_global_fun_aux params tagged_local_funs) tagged_data

/// If a global function contains some local function,
/// and the global function input decodes to a tag for this local function,
/// then the global function is equivalent to the local function on this input.

val local_eq_global_lemma:
  params:split_function_parameters ->
  global_fun:params.global_fun_t -> tag_set:params.tag_set_t -> local_fun:params.local_fun_t ->
  tagged_data:params.tagged_data_t -> tag:params.tag_t -> raw_data:params.raw_data_t ->
  Lemma
  (requires
    params.decode_tagged_data tagged_data == Some (tag, raw_data) /\
    tag `params.tag_belong_to` tag_set /\
    has_local_fun params global_fun (tag_set, local_fun)
  )
  (ensures params.apply_global_fun global_fun tagged_data == params.apply_local_fun local_fun raw_data)
let local_eq_global_lemma params global_fun tag_set tagged_local_fun tagged_data tag raw_data = ()

/// In the common case where tag disjointness is unequality,
/// the `no_repeats_p` predicate from F*'s standard library
/// implies `for_all_pairsP unequal`.
/// It is actually equivalent, but only this implication is useful.

val unequal:
  #a:Type ->
  a -> a -> prop
let unequal #a x y = x =!= y

val no_repeats_p_implies_for_all_pairsP_unequal:
  #a:Type ->
  l:list a ->
  Lemma
  (requires List.Tot.no_repeats_p l)
  (ensures for_all_pairsP unequal l)
let rec no_repeats_p_implies_for_all_pairsP_unequal #a l =
  match l with
  | [] -> ()
  | h::t ->
    no_repeats_p_implies_for_all_pairsP_unequal t;
    for_allP_eq (unequal h) t

/// In the common case tag sets are simple singletons,
/// these parameters can be used like this:
/// {
///   singleton_split_function_parameters string with
///   ...
/// }

let singleton_split_function_parameters (a:eqtype): split_function_parameters = {
  tag_set_t = a;
  tag_t = a;
  is_disjoint = unequal;
  tag_belong_to = (fun tag tag_set -> tag = tag_set);
  cant_belong_to_disjoint_sets = (fun tag tag_set1 tag_set2 -> ());

  // everything below should be redefined
  tagged_data_t = unit;
  raw_data_t = unit;
  output_t = unit;
  decode_tagged_data = (fun x -> None);

  local_fun_t = unit;
  global_fun_t = unit;

  default_global_fun = ();

  apply_local_fun = (fun lfun x -> ());
  apply_global_fun = (fun gfun x -> ());
  mk_global_fun = (fun bare -> ());
  apply_mk_global_fun = (fun bare x -> ());
}
