module DY.Lib.SplitFunction

open FStar.List.Tot

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
/// In practice, it may look like this:
/// let global_function param1 param2 param3 ... =
///   // First detect in which sub-component we are in
///   let tag = ... in
///   // then dispatch to the corresponding local function
///   match tag with
///   | ... -> local_fun1 ...
///   | ... -> local_fun2 ...
///   ...
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

noeq type split_function_input_values = {
  // Input type for the global function
  tagged_data_t: Type;

  // Two types of tag, that are related using `encode_tag`:
  // the tag type that we use to define the global function,
  // and the tag type that we obtain when decoding the global function input.
  // Having different types may be handy in some situations.
  tag_t: Type;
  encoded_tag_t: eqtype;

  // Input type for the local functions
  raw_data_t: Type;

  output_t: Type;

  // We can decode the global function input
  // into an encoded tag and a local function input
  decode_tagged_data: tagged_data_t -> Tot (option (encoded_tag_t & raw_data_t));

  // We can encode the tag, and this encoding must be injective.
  encode_tag: tag_t -> encoded_tag_t;
  encode_tag_inj: l1:tag_t -> l2:tag_t -> Lemma
    (requires encode_tag l1 == encode_tag l2)
    (ensures l1 == l2)
  ;

  // Types for the local functions and the global function
  local_fun: Type;
  global_fun: Type;

  default_global_fun: global_fun;

  // Apply a local function to its input
  apply_local_fun: local_fun -> raw_data_t -> output_t;
  // Apply the global function to its input
  apply_global_fun: global_fun -> tagged_data_t -> output_t;
  // Create a global function
  mk_global_fun: (tagged_data_t -> output_t) -> global_fun;
  // Correctness theorem on creating and applying a global function
  apply_mk_global_fun: bare:(tagged_data_t -> output_t) -> x:tagged_data_t -> Lemma
    (apply_global_fun (mk_global_fun bare) x == bare x);
}

/// Do a global function contain some given local function with some tag?
/// This will be a crucial precondition for the correctness theorem `local_eq_global_lemma`.

val has_local_fun: func:split_function_input_values -> func.global_fun -> (func.tag_t & func.local_fun) -> prop
let has_local_fun func gfun (the_tag, lfun) =
  forall tagged_data.
    match func.decode_tagged_data tagged_data with
    | Some (tag, raw_data) ->
      tag == func.encode_tag the_tag ==> (func.apply_global_fun gfun tagged_data == func.apply_local_fun lfun raw_data)
    | None -> True

val find_local_fun: func:split_function_input_values -> list (func.tag_t & func.local_fun) -> func.encoded_tag_t -> option func.local_fun
let rec find_local_fun func l tag =
  match l with
  | [] -> None
  | (the_tag, lfun)::t -> (
    if tag = func.encode_tag the_tag then
      Some lfun
    else
      find_local_fun func t tag
  )

val mk_global_fun_aux: func:split_function_input_values -> list (func.tag_t & func.local_fun) -> func.tagged_data_t -> func.output_t
let mk_global_fun_aux func l tagged_data =
  match func.decode_tagged_data tagged_data with
  | Some (tag, raw_data) -> (
    match find_local_fun func l tag with
    | Some lfun -> func.apply_local_fun lfun raw_data
    | None -> func.apply_global_fun func.default_global_fun tagged_data
  )
  | None -> func.apply_global_fun func.default_global_fun tagged_data

/// Given a list of tags and local functions, create the global function.

[@@"opaque_to_smt"]
val mk_global_fun: func:split_function_input_values -> list (func.tag_t & func.local_fun) -> func.global_fun
let mk_global_fun func l =
  func.mk_global_fun (mk_global_fun_aux func l)

val find_local_fun_wrong_tag:
  func:split_function_input_values ->
  the_tag:func.tag_t -> l:list (func.tag_t & func.local_fun) -> tag:func.encoded_tag_t ->
  Lemma
  (requires ~(List.Tot.memP the_tag (List.Tot.map fst l)))
  (ensures (
    tag == func.encode_tag the_tag ==> (find_local_fun func l tag == None)
  ))
let rec find_local_fun_wrong_tag func the_tag l tag =
  match l with
  | [] -> ()
  | (tag', _)::t -> (
    FStar.Classical.move_requires_2 func.encode_tag_inj the_tag tag';
    find_local_fun_wrong_tag func the_tag t tag
  )

val disjointP: #a:Type -> list a -> list a -> prop
let rec disjointP #a l1 l2 =
  match l2 with
  | [] -> True
  | h2::t2 ->
    ~(List.Tot.memP h2 l1) /\ disjointP l1 t2

val disjointP_move:
  #a:Type ->
  l1:list a -> x:a -> l2:list a ->
  Lemma
  (requires disjointP l1 l2 /\ ~(List.Tot.memP x l2))
  (ensures disjointP (l1 @ [x]) l2)
let rec disjointP_move #a l1 x l2 =
  match l2 with
  | [] -> ()
  | h2::t2 ->
    disjointP_move l1 x t2;
    List.Tot.append_memP l1 [x] h2;
    assert_norm(List.Tot.memP h2 [x] <==> h2 == x)

val find_local_fun_move:
  func:split_function_input_values ->
  lfuns1:list (func.tag_t & func.local_fun) -> x:(func.tag_t & func.local_fun) -> lfuns2:list (func.tag_t & func.local_fun) ->
  tag:func.encoded_tag_t ->
  Lemma
  (ensures
    (
      match find_local_fun func lfuns1 tag with
      | Some lfun -> Some lfun
      | None -> find_local_fun func (x::lfuns2) tag
    ) == (
      match find_local_fun func (lfuns1 @ [x]) tag with
      | Some lfun -> Some lfun
      | None -> find_local_fun func lfuns2 tag
    )
  )
let rec find_local_fun_move func lfuns1 (the_tag, the_sfun) lfuns2 tag =
  match lfuns1 with
  | [] -> ()
  | (h_tag, h_sfun)::t ->
    find_local_fun_move func t (the_tag, the_sfun) lfuns2 tag

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

val mk_global_fun_correct_aux:
  func:split_function_input_values -> gfun:(func.encoded_tag_t -> option func.local_fun) -> lfuns1:list (func.tag_t & func.local_fun) -> lfuns2:list (func.tag_t & func.local_fun) -> the_tag:func.tag_t -> lfun:func.local_fun -> tag:func.encoded_tag_t ->
  Lemma
  (requires
    (forall tag. gfun tag == (
        match find_local_fun func lfuns1 tag with
        | Some lfun -> Some lfun
        | None -> (
          match find_local_fun func lfuns2 tag with
          | Some lfun -> Some lfun
          | None -> None
        )
      )
    ) /\
    List.Tot.no_repeats_p (List.Tot.map fst lfuns2) /\
    disjointP (List.Tot.map fst lfuns1) (List.Tot.map fst lfuns2) /\
    tag == func.encode_tag the_tag /\
    List.Tot.memP (the_tag, lfun) lfuns2
  )
  (ensures gfun tag == Some lfun)
  (decreases List.Tot.length lfuns2)
let rec mk_global_fun_correct_aux func gfun lfuns1 lfuns2 the_tag lfun tag =
  match lfuns2 with
  | [] -> ()
  | (h_tag, h_sfun)::t -> (
    eliminate h_tag == the_tag \/ h_tag =!= the_tag returns gfun tag == Some lfun with _. (
      find_local_fun_wrong_tag func the_tag lfuns1 tag;
      FStar.Classical.move_requires_3 memP_map fst t (the_tag, lfun)
    ) and _. (
      disjointP_move (List.Tot.map fst lfuns1) h_tag (List.Tot.map fst t);
      List.Tot.map_append fst lfuns1 [(h_tag, h_sfun)];
      assert_norm(List.Tot.map fst [(h_tag, h_sfun)] == [h_tag]);
      FStar.Classical.forall_intro (find_local_fun_move func lfuns1 (h_tag, h_sfun) t);
      mk_global_fun_correct_aux func gfun (lfuns1 @ [(h_tag, h_sfun)]) t the_tag lfun tag
    )
  )

val disjointP_nil: #a:Type -> l:list a -> Lemma (disjointP [] l)
let rec disjointP_nil #a l =
  match l with
  | [] -> ()
  | _::t -> disjointP_nil t

/// Correctness theorem for `mk_global_fun`:
/// the global function contains all the local functions used to construct it.

val mk_global_fun_correct:
  func:split_function_input_values -> lfuns:list (func.tag_t & func.local_fun) -> the_tag:func.tag_t -> lfun:func.local_fun ->
  Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst lfuns) /\
    List.Tot.memP (the_tag, lfun) lfuns
  )
  (ensures has_local_fun func (mk_global_fun func lfuns) (the_tag, lfun))
let mk_global_fun_correct func lfuns the_tag lfun =
  reveal_opaque (`%mk_global_fun) (mk_global_fun);
  introduce
    forall tagged_data.
      match func.decode_tagged_data tagged_data with
      | Some (tag, raw_data) ->
        tag == func.encode_tag the_tag ==> (func.apply_global_fun (mk_global_fun func lfuns) tagged_data == func.apply_local_fun lfun raw_data)
      | None -> True
  with (
    match func.decode_tagged_data tagged_data with
    | Some (tag, raw_data) -> (
      if tag = func.encode_tag the_tag then (
        disjointP_nil (List.Tot.map fst lfuns);
        mk_global_fun_correct_aux func (find_local_fun func lfuns) [] lfuns the_tag lfun tag;
        func.apply_mk_global_fun (mk_global_fun_aux func lfuns) tagged_data
      ) else ()
    )
    | None -> ()
  )

/// Equivalence theorem for `mk_global_fun`.
/// This may be useful to lift properties of the local functions
/// to property on the global function.
/// (e.g. the function keep the same output when the trace grows.)

val mk_global_fun_eq:
  func:split_function_input_values -> lfuns:list (func.tag_t & func.local_fun) ->
  tagged_data:func.tagged_data_t ->
  Lemma (
    func.apply_global_fun (mk_global_fun func lfuns) tagged_data == (
      match func.decode_tagged_data tagged_data with
      | Some (tag, raw_data) -> (
        match find_local_fun func lfuns tag with
        | Some lfun -> func.apply_local_fun lfun raw_data
        | None -> func.apply_global_fun func.default_global_fun tagged_data
      )
      | None -> func.apply_global_fun func.default_global_fun tagged_data
    )
  )
let mk_global_fun_eq func lfuns tagged_data =
  reveal_opaque (`%mk_global_fun) (mk_global_fun);
  func.apply_mk_global_fun (mk_global_fun_aux func lfuns) tagged_data

/// If a global function contains some local function,
/// and the global function input decodes to a tag for this local function,
/// then the global function is equivalent to the local function on this input.

val local_eq_global_lemma:
  func:split_function_input_values ->
  gfun:func.global_fun -> the_tag:func.tag_t -> lfun:func.local_fun ->
  tagged_data:func.tagged_data_t -> raw_data:func.raw_data_t ->
  Lemma
  (requires
    func.decode_tagged_data tagged_data == Some (func.encode_tag the_tag, raw_data) /\
    has_local_fun func gfun (the_tag, lfun)
  )
  (ensures func.apply_global_fun gfun tagged_data == func.apply_local_fun lfun raw_data)
let local_eq_global_lemma func gfun the_tag lfun tagged_data raw_data = ()
