module DY.Lib.SplitPredicate

#set-options "--fuel 1 --ifuel 1"

// Some kind of cheap module functor like ocaml but in F*
noeq type split_predicate_input_values = {
  labeled_data_t: Type;
  label_t: Type;
  encoded_label_t: Type;
  raw_data_t: Type;

  decode_labeled_data: labeled_data_t -> GTot (option (encoded_label_t & raw_data_t));

  encode_label: label_t -> encoded_label_t;
  encode_label_inj: l1:label_t -> l2:label_t -> Lemma
    (requires encode_label l1 == encode_label l2)
    (ensures l1 == l2)
  ;

  local_pred:Type;
  global_pred:Type;
  apply_local_pred: local_pred -> raw_data_t -> prop;
  apply_global_pred: global_pred -> labeled_data_t -> prop;
  mk_global_pred: (labeled_data_t -> prop) -> global_pred;
  apply_mk_global_pred: bare:(labeled_data_t -> prop) -> x:labeled_data_t -> Lemma
    (apply_global_pred (mk_global_pred bare) x == bare x)
}

// Can probably be generalized to handle kdf usage too?
type bare_global_pred (func:split_predicate_input_values) =
  func.labeled_data_t -> prop
type bare_local_pred (func:split_predicate_input_values) =
  func.raw_data_t -> prop

val has_local_pred: func:split_predicate_input_values -> func.global_pred -> func.label_t -> func.local_pred -> prop
let has_local_pred func gpred the_label lpred =
  forall labeled_data.
    match func.decode_labeled_data labeled_data with
    | Some (label, raw_data) ->
      label == func.encode_label the_label ==> (func.apply_global_pred gpred labeled_data <==> func.apply_local_pred lpred raw_data)
    | None -> True

val mk_global_pred_aux: func:split_predicate_input_values -> list (func.label_t & func.local_pred) -> bare_global_pred func
let rec mk_global_pred_aux func l labeled_data =
  match l with
  | [] -> False
  | (the_label, lpred)::t ->
    let cur_prop =
      match func.decode_labeled_data labeled_data with
      | Some (label, raw_data) ->
        label == func.encode_label the_label /\ func.apply_local_pred lpred raw_data
      | None -> False
    in
    cur_prop \/ mk_global_pred_aux func t labeled_data

val mk_global_pred: func:split_predicate_input_values -> list (func.label_t & func.local_pred) -> func.global_pred
let mk_global_pred func l =
  func.mk_global_pred (mk_global_pred_aux func l)

val mk_global_pred_aux_wrong_label:
  func:split_predicate_input_values ->
  the_label:func.label_t -> l:list (func.label_t & func.local_pred) -> labeled_data:func.labeled_data_t ->
  Lemma
  (requires ~(List.Tot.memP the_label (List.Tot.map fst l)))
  (ensures (
    match func.decode_labeled_data labeled_data with
    | Some (label, raw_data) ->
      label == func.encode_label the_label ==> ~(mk_global_pred_aux func l labeled_data)
    | None -> ~(mk_global_pred_aux func l labeled_data)
  ))
let rec mk_global_pred_aux_wrong_label func the_label l labeled_data =
  match l with
  | [] -> ()
  | (label, _)::t -> (
    FStar.Classical.move_requires_2 func.encode_label_inj the_label label;
    mk_global_pred_aux_wrong_label func the_label t labeled_data
  )

val disjointP: #a:Type -> list a -> list a -> prop
let rec disjointP #a l1 l2 =
  match l1 with
  | [] -> True
  | h1::t1 ->
    ~(List.Tot.memP h1 l2) /\ disjointP t1 l2

val disjointP_cons:
  #a:Type ->
  x:a -> l1:list a -> l2:list a ->
  Lemma
  (requires disjointP l1 l2 /\ ~(List.Tot.memP x l1))
  (ensures disjointP l1 (x::l2))
let rec disjointP_cons #a x l1 l2 =
  match l1 with
  | [] -> ()
  | h1::t1 -> disjointP_cons x t1 l2

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
  func:split_predicate_input_values -> gpred:bare_global_pred func -> lpreds1:list (func.label_t & func.local_pred) -> lpreds2:list (func.label_t & func.local_pred) -> the_label:func.label_t -> lpred:func.local_pred ->
  Lemma
  (requires
    (forall labeled_data. (mk_global_pred_aux func lpreds1 labeled_data \/ mk_global_pred_aux func lpreds2 labeled_data) <==> gpred labeled_data) /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds1) /\
    disjointP (List.Tot.map fst lpreds1) (List.Tot.map fst lpreds2) /\
    List.Tot.memP (the_label, lpred) lpreds1
  )
  (ensures has_local_pred func (func.mk_global_pred gpred) the_label lpred)
let rec mk_global_pred_correct_aux func gpred lpreds1 lpreds2 the_label lpred =
  match lpreds1 with
  | [] -> ()
  | (h_lab, h_spred)::t -> (
    eliminate h_lab == the_label \/ h_lab =!= the_label returns has_local_pred func (func.mk_global_pred gpred) the_label lpred with _. (
      introduce forall labeled_data. (
        match func.decode_labeled_data labeled_data with
        | Some (label, raw_data) ->
          label == func.encode_label the_label ==> (gpred labeled_data <==> func.apply_local_pred lpred raw_data)
        | None -> True
      ) with (
        match func.decode_labeled_data labeled_data with
        | Some (label, raw_data) -> (
          eliminate label == func.encode_label the_label \/ label =!= func.encode_label the_label returns _ with _. (
            func.encode_label_inj the_label h_lab;
            mk_global_pred_aux_wrong_label func the_label t labeled_data;
            mk_global_pred_aux_wrong_label func the_label lpreds2 labeled_data;
            FStar.Classical.move_requires_3 memP_map fst t (the_label, lpred)
          ) and _. ()
        )
        | None -> ()
      );
      FStar.Classical.forall_intro (func.apply_mk_global_pred gpred)
    ) and _. (
      disjointP_cons h_lab (List.Tot.map fst t) (List.Tot.map fst lpreds2);
      mk_global_pred_correct_aux func gpred t ((h_lab, h_spred)::lpreds2) the_label lpred
    )
  )

val disjointP_nil: #a:Type -> l:list a -> Lemma (disjointP l [])
let rec disjointP_nil #a l =
  match l with
  | [] -> ()
  | _::t -> disjointP_nil t

val mk_global_pred_correct:
  func:split_predicate_input_values -> lpreds:list (func.label_t & func.local_pred) -> the_label:func.label_t -> lpred:func.local_pred ->
  Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst lpreds) /\
    List.Tot.memP (the_label, lpred) lpreds
  )
  (ensures has_local_pred func (mk_global_pred func lpreds) the_label lpred)
let mk_global_pred_correct func lpreds the_label lpred =
  disjointP_nil (List.Tot.map fst lpreds);
  mk_global_pred_correct_aux func (mk_global_pred_aux func lpreds) lpreds [] the_label lpred

val mk_global_pred_eq_aux:
  func:split_predicate_input_values -> lpreds:list (func.label_t & func.local_pred) ->
  labeled_data:func.labeled_data_t ->
  Lemma
  ((mk_global_pred_aux func lpreds) labeled_data <==> (
      exists lab lpred raw_data.
        List.Tot.memP (lab, lpred) lpreds /\
        func.apply_local_pred lpred raw_data /\
        func.decode_labeled_data labeled_data == Some (func.encode_label lab, raw_data)
    )
  )
let rec mk_global_pred_eq_aux func lpreds labeled_data =
  match lpreds with
  | [] -> ()
  | (the_label, lpred)::tpreds ->
    mk_global_pred_eq_aux func tpreds labeled_data;
    match func.decode_labeled_data labeled_data with
    | None -> ()
    | Some (label, raw_data) -> ()

val mk_global_pred_eq:
  func:split_predicate_input_values -> lpreds:list (func.label_t & func.local_pred) ->
  labeled_data:func.labeled_data_t ->
  Lemma
  (func.apply_global_pred (mk_global_pred func lpreds) labeled_data <==> (
      exists lab lpred raw_data.
        List.Tot.memP (lab, lpred) lpreds /\
        func.apply_local_pred lpred raw_data /\
        func.decode_labeled_data labeled_data == Some (func.encode_label lab, raw_data)
    )
  )
let mk_global_pred_eq func lpreds labeled_data =
  func.apply_mk_global_pred (mk_global_pred_aux func lpreds) labeled_data;
  mk_global_pred_eq_aux func lpreds labeled_data

val local_eq_global_lemma:
  func:split_predicate_input_values ->
  gpred:func.global_pred -> the_label:func.label_t -> lpred:func.local_pred ->
  labeled_data:func.labeled_data_t -> raw_data:func.raw_data_t ->
  Lemma
  (requires
    func.decode_labeled_data labeled_data == Some (func.encode_label the_label, raw_data) /\
    has_local_pred func gpred the_label lpred
  )
  (ensures func.apply_global_pred gpred labeled_data <==> func.apply_local_pred lpred raw_data)
let local_eq_global_lemma func gpred the_label lpred labeled_data raw_data = ()
