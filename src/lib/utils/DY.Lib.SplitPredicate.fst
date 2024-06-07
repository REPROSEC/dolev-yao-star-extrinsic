module DY.Lib.SplitPredicate

open FStar.List.Tot

#set-options "--fuel 1 --ifuel 1"

/// This module defines a library to create a global predicate from several independent local predicates,
/// also called the "split predicate methodology".
///
/// DY* proofs rely on global protocol invariants
/// (e.g. what protocol participants are allowed to store, or are allowed to sign),
/// that must be preserved by each step of the protocol.
/// The practice of defining this global protocol invariant monolithically somewhere has a few drawbacks:
/// - it does not allows the user to do modular proofs,
///   as many unrelated predicates are put in the same place
/// - when modifying the global predicate for some sub-component,
///   other unrelated sub-components will need to be re-checked
///   (because the global predicate they depend on has changed)
///   (and their proof might fail if the SMT gods are angry!)
/// - it makes it difficult to create reusable components
///   (such as a generic state to store private keys)
///
/// With this module, we can create a global predicate from several independent local predicates (see mk_global_pred).
/// Then, proofs of theorems will take as parameter some global predicate,
/// with the precondition that it contains a specific local predicate (see has_local_pred).
/// In this way, proofs will work for any global predicate
/// as long as it contains the relevant local predicate.
/// (This is in contrast to proofs reyling on
/// a monolithic global predicate
/// that is defined at the top of a file (using val and let).)
///
/// This solves all the problems mentioned above:
/// predicates are defined (locally) where they belong,
/// proofs are modular because they only depend on
/// the relevant local predicate being contained in the global predicate
/// (a property that is not affected by other unrelated local predicates).
///
/// Under the hood, the split predicate methodology
/// is simply factorizing out a common pattern we see
/// when writing monolithic global predicates.
/// Indeed, such a monolithic global predicate usually
/// - first disambiguate to which local predicate its input belong to
/// - then dispatch the input to that local predicate, maybe after some modifications.
/// In practice, it may look like this:
/// let global_predicate param1 param2 param3 ... =
///   // First detect in which sub-component we are in
///   let tag = ... in
///   // then dispatch to the corresponding local predicate
///   match tag with
///   | ... -> local_pred1 ...
///   | ... -> local_pred2 ...
///   ...
/// The tag may be obtained in different ways,
/// for example with the key usage (e.g. for a signature predicate, see DY.Core.Bytes.Type.usage),
/// or because some messages are tagged
/// (e.g. the state content in a state predicate or the signature input in signature predicate).
/// How to obtain this tag is not always trivial,
/// it is actually a core argument in the proof of
/// why it is secure to deploy different sub-components in parallel.
///
/// The split predicate methodology can be used to implement horizontal composition:
/// as long as we can find a way to disambiguate the composed protocols (using the tag),
/// we can easily construct a global predicate implementing this horizontal composition.

/// The parameters of the split predicate methodology.

noeq type split_predicate_input_values = {
  // Input type for the global predicate
  tagged_data_t: Type;

  // Two types of tag, that are related using `encode_tag`:
  // the tag type that we use to define the global predicate,
  // and the tag type that we obtain when decoding the global predicate input.
  // Having different types may be handy in some situations.
  tag_t: Type;
  encoded_tag_t: eqtype;

  // Input type for the local predicates
  raw_data_t: Type;

  output_t: Type;

  // We can decode the global predicate input
  // into an encoded tag and a local predicate input
  decode_tagged_data: tagged_data_t -> Tot (option (encoded_tag_t & raw_data_t));

  // We can encode the tag, and this encoding must be injective.
  encode_tag: tag_t -> encoded_tag_t;
  encode_tag_inj: l1:tag_t -> l2:tag_t -> Lemma
    (requires encode_tag l1 == encode_tag l2)
    (ensures l1 == l2)
  ;

  // Types for the local predicates and the global predicate
  local_pred: Type;
  global_pred: Type;

  default_global_pred: global_pred;

  // Apply a local predicate to its input
  apply_local_pred: local_pred -> raw_data_t -> output_t;
  // Apply the global predicate to its input
  apply_global_pred: global_pred -> tagged_data_t -> output_t;
  // Create a global predicate
  mk_global_pred: (tagged_data_t -> output_t) -> global_pred;
  // Correctness theorem on creating and applying a global predicate
  apply_mk_global_pred: bare:(tagged_data_t -> output_t) -> x:tagged_data_t -> Lemma
    (apply_global_pred (mk_global_pred bare) x == bare x);
}

/// Do a global predicate contain some given local predicate with some tag?
/// This will be a crucial precondition for the correctness theorem `local_eq_global_lemma`.

val has_local_pred: func:split_predicate_input_values -> func.global_pred -> (func.tag_t & func.local_pred) -> prop
let has_local_pred func gpred (the_tag, lpred) =
  forall tagged_data.
    match func.decode_tagged_data tagged_data with
    | Some (tag, raw_data) ->
      tag == func.encode_tag the_tag ==> (func.apply_global_pred gpred tagged_data == func.apply_local_pred lpred raw_data)
    | None -> True

val find_local_pred: func:split_predicate_input_values -> list (func.tag_t & func.local_pred) -> func.encoded_tag_t -> option func.local_pred
let rec find_local_pred func l tag =
  match l with
  | [] -> None
  | (the_tag, lpred)::t -> (
    if tag = func.encode_tag the_tag then
      Some lpred
    else
      find_local_pred func t tag
  )

val mk_global_pred_aux: func:split_predicate_input_values -> list (func.tag_t & func.local_pred) -> func.tagged_data_t -> func.output_t
let mk_global_pred_aux func l tagged_data =
  match func.decode_tagged_data tagged_data with
  | Some (tag, raw_data) -> (
    match find_local_pred func l tag with
    | Some lpred -> func.apply_local_pred lpred raw_data
    | None -> func.apply_global_pred func.default_global_pred tagged_data
  )
  | None -> func.apply_global_pred func.default_global_pred tagged_data

/// Given a list of tags and local predicates, create the global predicate.

[@@"opaque_to_smt"]
val mk_global_pred: func:split_predicate_input_values -> list (func.tag_t & func.local_pred) -> func.global_pred
let mk_global_pred func l =
  func.mk_global_pred (mk_global_pred_aux func l)

val find_local_pred_wrong_tag:
  func:split_predicate_input_values ->
  the_tag:func.tag_t -> l:list (func.tag_t & func.local_pred) -> tag:func.encoded_tag_t ->
  Lemma
  (requires ~(List.Tot.memP the_tag (List.Tot.map fst l)))
  (ensures (
    tag == func.encode_tag the_tag ==> (find_local_pred func l tag == None)
  ))
let rec find_local_pred_wrong_tag func the_tag l tag =
  match l with
  | [] -> ()
  | (tag', _)::t -> (
    FStar.Classical.move_requires_2 func.encode_tag_inj the_tag tag';
    find_local_pred_wrong_tag func the_tag t tag
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

val find_local_pred_move:
  func:split_predicate_input_values ->
  lpreds1:list (func.tag_t & func.local_pred) -> x:(func.tag_t & func.local_pred) -> lpreds2:list (func.tag_t & func.local_pred) ->
  tag:func.encoded_tag_t ->
  Lemma
  (ensures
    (
      match find_local_pred func lpreds1 tag with
      | Some lpred -> Some lpred
      | None -> find_local_pred func (x::lpreds2) tag
    ) == (
      match find_local_pred func (lpreds1 @ [x]) tag with
      | Some lpred -> Some lpred
      | None -> find_local_pred func lpreds2 tag
    )
  )
let rec find_local_pred_move func lpreds1 (the_tag, the_spred) lpreds2 tag =
  match lpreds1 with
  | [] -> ()
  | (h_tag, h_spred)::t ->
    find_local_pred_move func t (the_tag, the_spred) lpreds2 tag

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

val mk_global_pred_correct_aux:
  func:split_predicate_input_values -> gpred:(func.encoded_tag_t -> option func.local_pred) -> lpreds1:list (func.tag_t & func.local_pred) -> lpreds2:list (func.tag_t & func.local_pred) -> the_tag:func.tag_t -> lpred:func.local_pred -> tag:func.encoded_tag_t ->
  Lemma
  (requires
    (forall tag. gpred tag == (
        match find_local_pred func lpreds1 tag with
        | Some lpred -> Some lpred
        | None -> (
          match find_local_pred func lpreds2 tag with
          | Some lpred -> Some lpred
          | None -> None
        )
      )
    ) /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds2) /\
    disjointP (List.Tot.map fst lpreds1) (List.Tot.map fst lpreds2) /\
    tag == func.encode_tag the_tag /\
    List.Tot.memP (the_tag, lpred) lpreds2
  )
  (ensures gpred tag == Some lpred)
  (decreases List.Tot.length lpreds2)
let rec mk_global_pred_correct_aux func gpred lpreds1 lpreds2 the_tag lpred tag =
  match lpreds2 with
  | [] -> ()
  | (h_tag, h_spred)::t -> (
    eliminate h_tag == the_tag \/ h_tag =!= the_tag returns gpred tag == Some lpred with _. (
      find_local_pred_wrong_tag func the_tag lpreds1 tag;
      FStar.Classical.move_requires_3 memP_map fst t (the_tag, lpred)
    ) and _. (
      disjointP_move (List.Tot.map fst lpreds1) h_tag (List.Tot.map fst t);
      List.Tot.map_append fst lpreds1 [(h_tag, h_spred)];
      assert_norm(List.Tot.map fst [(h_tag, h_spred)] == [h_tag]);
      FStar.Classical.forall_intro (find_local_pred_move func lpreds1 (h_tag, h_spred) t);
      mk_global_pred_correct_aux func gpred (lpreds1 @ [(h_tag, h_spred)]) t the_tag lpred tag
    )
  )

val disjointP_nil: #a:Type -> l:list a -> Lemma (disjointP [] l)
let rec disjointP_nil #a l =
  match l with
  | [] -> ()
  | _::t -> disjointP_nil t

/// Correctness theorem for `mk_global_pred`:
/// the global predicate contains all the local predicates used to construct it.

val mk_global_pred_correct:
  func:split_predicate_input_values -> lpreds:list (func.tag_t & func.local_pred) -> the_tag:func.tag_t -> lpred:func.local_pred ->
  Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst lpreds) /\
    List.Tot.memP (the_tag, lpred) lpreds
  )
  (ensures has_local_pred func (mk_global_pred func lpreds) (the_tag, lpred))
let mk_global_pred_correct func lpreds the_tag lpred =
  reveal_opaque (`%mk_global_pred) (mk_global_pred);
  introduce
    forall tagged_data.
      match func.decode_tagged_data tagged_data with
      | Some (tag, raw_data) ->
        tag == func.encode_tag the_tag ==> (func.apply_global_pred (mk_global_pred func lpreds) tagged_data == func.apply_local_pred lpred raw_data)
      | None -> True
  with (
    match func.decode_tagged_data tagged_data with
    | Some (tag, raw_data) -> (
      if tag = func.encode_tag the_tag then (
        disjointP_nil (List.Tot.map fst lpreds);
        mk_global_pred_correct_aux func (find_local_pred func lpreds) [] lpreds the_tag lpred tag;
        func.apply_mk_global_pred (mk_global_pred_aux func lpreds) tagged_data
      ) else ()
    )
    | None -> ()
  )

/// Equivalence theorem for `mk_global_pred`.
/// This may be useful to lift properties of the local predicates
/// to property on the global predicate.
/// (e.g. the predicate stays true when the trace grows.)

val mk_global_pred_eq:
  func:split_predicate_input_values -> lpreds:list (func.tag_t & func.local_pred) ->
  tagged_data:func.tagged_data_t ->
  Lemma (
    func.apply_global_pred (mk_global_pred func lpreds) tagged_data == (
      match func.decode_tagged_data tagged_data with
      | Some (tag, raw_data) -> (
        match find_local_pred func lpreds tag with
        | Some lpred -> func.apply_local_pred lpred raw_data
        | None -> func.apply_global_pred func.default_global_pred tagged_data
      )
      | None -> func.apply_global_pred func.default_global_pred tagged_data
    )
  )
let mk_global_pred_eq func lpreds tagged_data =
  reveal_opaque (`%mk_global_pred) (mk_global_pred);
  func.apply_mk_global_pred (mk_global_pred_aux func lpreds) tagged_data

/// If a global predicate contains some local predicate,
/// and the global predicate input decodes to a tag for this local predicate,
/// then the global predicate is equivalent to the local predicate on this input.

val local_eq_global_lemma:
  func:split_predicate_input_values ->
  gpred:func.global_pred -> the_tag:func.tag_t -> lpred:func.local_pred ->
  tagged_data:func.tagged_data_t -> raw_data:func.raw_data_t ->
  Lemma
  (requires
    func.decode_tagged_data tagged_data == Some (func.encode_tag the_tag, raw_data) /\
    has_local_pred func gpred (the_tag, lpred)
  )
  (ensures func.apply_global_pred gpred tagged_data == func.apply_local_pred lpred raw_data)
let local_eq_global_lemma func gpred the_tag lpred tagged_data raw_data = ()
