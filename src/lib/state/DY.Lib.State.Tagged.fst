module DY.Lib.State.Tagged

open Comparse
open DY.Core
open DY.Lib.SplitFunction
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

#set-options "--fuel 1 --ifuel 1"

(*** Tagged state predicates ***)

[@@ with_bytes bytes]
type tagged_state = {
  [@@@ with_parser #bytes ps_string]
  tag: string;
  content: bytes;
}

%splice [ps_tagged_state] (gen_parser (`tagged_state))
%splice [ps_tagged_state_is_well_formed] (gen_is_well_formed_lemma (`tagged_state))

instance parseable_serializeable_bytes_tagged_state: parseable_serializeable bytes tagged_state = mk_parseable_serializeable (ps_tagged_state)

val tagged_state_pred_label_input: Type u#1
let tagged_state_pred_label_input =
  principal -> string -> state_id -> bytes -> prop

val compile_tagged_state_pred_label_input:
  tagged_state_pred_label_input ->
  state_pred_label_input
let compile_tagged_state_pred_label_input p prin sess_id full_content =
  match parse tagged_state full_content with
  | None -> False
  | Some {tag; content} ->
    p prin tag sess_id content

val tagged_state_pred_label:
  tagged_state_pred_label_input ->
  label
let tagged_state_pred_label p =
  state_pred_label (compile_tagged_state_pred_label_input p)

val tagged_state_was_corrupt:
  trace ->
  principal -> string -> state_id -> bytes ->
  prop
let tagged_state_was_corrupt tr prin tag sid content =
  DY.Core.state_was_corrupt tr prin sid (serialize tagged_state {
    tag;
    content = content;
  })

// This lemma is useful to keep ifuel low
// when reasoning on `tagged_state_pred_label`.
val tagged_state_pred_label_input_allow_inversion:
  p1:tagged_state_pred_label_input ->
  p2:state_pred_label_input ->
  Lemma (
    inversion (option tagged_state) /\
    inversion tagged_state
  )
  [SMTPatOr [
    [SMTPat (state_pred_label_input_can_flow p2 (compile_tagged_state_pred_label_input p1))];
    [SMTPat (state_pred_label_input_can_flow (compile_tagged_state_pred_label_input p1) p2)];
  ]]
let tagged_state_pred_label_input_allow_inversion p1 p2 =
  allow_inversion (option tagged_state);
  allow_inversion (tagged_state)

val tagged_state_pred_label_can_flow_public:
  tr:trace ->
  p:tagged_state_pred_label_input ->
  Lemma (
    tagged_state_pred_label p `can_flow tr` public
    <==> (
      exists prin tag sid content.
        tagged_state_was_corrupt tr prin tag sid content /\
        p prin tag sid content
    )
  )
let tagged_state_pred_label_can_flow_public tr p =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (serialize_parse_inv_lemma #bytes tagged_state));
  state_pred_label_can_flow_public tr (compile_tagged_state_pred_label_input p)

val principal_tag_state_content_label_input:
  principal -> string -> state_id -> bytes ->
  tagged_state_pred_label_input
let principal_tag_state_content_label_input prin1 sess_id1 tag1 content1 =
  fun prin2 sess_id2 tag2 content2 ->
    prin1 == prin2 /\
    sess_id1 == sess_id2 /\
    tag1 == tag2 /\
    content1 == content2

val principal_tag_state_content_label: principal -> string -> state_id -> bytes -> label
let principal_tag_state_content_label prin tag sess_id content =
  tagged_state_pred_label (principal_tag_state_content_label_input prin tag sess_id content)

val principal_tag_state_label_input:
  principal -> string -> state_id ->
  tagged_state_pred_label_input
let principal_tag_state_label_input prin1 tag1 sess_id1 =
  fun prin2 tag2 sess_id2 _ ->
    prin1 == prin2 /\
    tag1 == tag2 /\
    sess_id1 == sess_id2

val principal_tag_state_label: principal -> string -> state_id -> label
let principal_tag_state_label prin tag sess_id =
  tagged_state_pred_label (principal_tag_state_label_input prin tag sess_id)

val principal_tag_label_input:
  principal -> string ->
  tagged_state_pred_label_input
let principal_tag_label_input prin1 tag1 =
  fun prin2 tag2 _ _ ->
    prin1 == prin2 /\
    tag1 == tag2

val principal_tag_label: principal -> string -> label
let principal_tag_label prin tag =
  tagged_state_pred_label (principal_tag_label_input prin tag)

noeq
type local_bytes_state_predicate {|crypto_invariants|} (tag:string) = {
  pred: trace -> principal -> state_id -> bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:state_id -> content:bytes ->
    Lemma
    (requires pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id content)
  ;
  pred_knowable:
    tr:trace -> prin:principal -> sess_id:state_id -> content:bytes ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures is_knowable_by (principal_tag_state_content_label prin tag sess_id content) tr content)
  ;
}

let split_local_bytes_state_predicate_params {|crypto_invariants|} : split_function_parameters = {
  singleton_split_function_parameters string with

  tagged_data_t = trace & principal & state_id & bytes;
  raw_data_t = trace & principal & state_id & bytes;
  output_t = prop;

  decode_tagged_data = (fun (tr, prin, sess_id, sess_content) -> (
    match parse tagged_state sess_content with
    | Some ({tag; content}) -> Some (tag, (tr, prin, sess_id, content))
    | None -> None
  ));

  local_fun_t = local_bytes_state_predicate;
  global_fun_t = trace -> principal -> state_id -> bytes -> prop;

  default_global_fun = (fun tr prin sess_id sess_content -> False);

  apply_local_fun = (fun lpred (tr, prin, sess_id, content) ->
    lpred.pred tr prin sess_id content
  );
  apply_global_fun = (fun gpred (tr, prin, sess_id, content) ->
    gpred tr prin sess_id content
  );
  mk_global_fun = (fun bare -> fun tr prin sess_id content ->
    bare (tr, prin, sess_id, content)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

[@@ "opaque_to_smt"]
val has_local_bytes_state_predicate: {|protocol_invariants|} -> (dtuple2 string local_bytes_state_predicate) -> prop
let has_local_bytes_state_predicate #invs (|tag, spred|) =
  has_local_fun split_local_bytes_state_predicate_params state_pred.pred (|tag, spred|)

(*** Global tagged state predicate builder ***)

val mk_global_local_bytes_state_predicate: {|crypto_invariants|} -> list (dtuple2 string local_bytes_state_predicate) -> trace -> principal -> state_id -> bytes -> prop
let mk_global_local_bytes_state_predicate #cinvs tagged_local_preds =
  mk_global_fun split_local_bytes_state_predicate_params tagged_local_preds

#push-options "--ifuel 2" // to deconstruct nested tuples
val mk_global_local_bytes_state_predicate_later:
  {|crypto_invariants|} -> tagged_local_preds:list (dtuple2 string local_bytes_state_predicate) ->
  tr1:trace -> tr2:trace -> prin:principal -> sess_id:state_id -> full_content:bytes -> Lemma
  (requires mk_global_local_bytes_state_predicate tagged_local_preds tr1 prin sess_id full_content /\ tr1 <$ tr2)
  (ensures mk_global_local_bytes_state_predicate tagged_local_preds tr2 prin sess_id full_content)
let mk_global_local_bytes_state_predicate_later #cinvs tagged_local_preds tr1 tr2 prin sess_id full_content =
  mk_global_fun_eq split_local_bytes_state_predicate_params tagged_local_preds (tr1, prin, sess_id, full_content);
  mk_global_fun_eq split_local_bytes_state_predicate_params tagged_local_preds (tr2, prin, sess_id, full_content);
  introduce forall tag_set lpred content. split_local_bytes_state_predicate_params.apply_local_fun #tag_set lpred (tr1, prin, sess_id, content) ==> split_local_bytes_state_predicate_params.apply_local_fun lpred (tr2, prin, sess_id, content) with (
    introduce _ ==> _ with _. lpred.pred_later tr1 tr2 prin sess_id content
  )
#pop-options

val mk_global_local_bytes_state_predicate_knowable:
  {|crypto_invariants|} -> tagged_local_preds:list (dtuple2 string local_bytes_state_predicate) ->
  tr:trace -> prin:principal -> sess_id:state_id -> full_content:bytes ->
  Lemma
  (requires mk_global_local_bytes_state_predicate tagged_local_preds tr prin sess_id full_content)
  (ensures is_knowable_by (principal_state_content_label prin sess_id full_content) tr full_content)
let mk_global_local_bytes_state_predicate_knowable #cinvs tagged_local_preds tr prin sess_id full_content =
  mk_global_fun_eq split_local_bytes_state_predicate_params tagged_local_preds (tr, prin, sess_id, full_content);
  match split_local_bytes_state_predicate_params.decode_tagged_data (tr, prin, sess_id, full_content) with
  | Some (tag, (_, _, _, content)) -> (
    match find_local_fun split_local_bytes_state_predicate_params tagged_local_preds tag with
    | Some (|_, lpred|) -> (
      find_local_fun_returns_belonging_tag_set split_local_bytes_state_predicate_params tagged_local_preds tag;
      lpred.pred_knowable tr prin sess_id content;
      serialize_parse_inv_lemma tagged_state full_content;
      serialize_wf_lemma tagged_state (is_knowable_by (principal_tag_state_content_label prin tag sess_id content) tr) ({tag; content})
    )
    | None -> ()
  )
  | None -> ()

val mk_state_pred: {|crypto_invariants|} -> list (dtuple2 string local_bytes_state_predicate) -> state_predicate
let mk_state_pred #cinvs tagged_local_preds =
  {
    pred = mk_global_local_bytes_state_predicate tagged_local_preds;
    pred_later = mk_global_local_bytes_state_predicate_later tagged_local_preds;
    pred_knowable = mk_global_local_bytes_state_predicate_knowable tagged_local_preds;
  }

val mk_state_pred_correct: {|protocol_invariants|} -> tagged_local_preds:list (dtuple2 string local_bytes_state_predicate) -> Lemma
  (requires
    state_pred == mk_state_pred tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map dfst tagged_local_preds)
  )
  (ensures for_allP has_local_bytes_state_predicate tagged_local_preds)
let mk_state_pred_correct #invs tagged_local_preds =
  reveal_opaque (`%has_local_bytes_state_predicate) (has_local_bytes_state_predicate);
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map dfst tagged_local_preds);
  for_allP_eq has_local_bytes_state_predicate tagged_local_preds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_local_bytes_state_predicate_params tagged_local_preds))

(*** Predicates on trace ***)

[@@ "opaque_to_smt"]
val tagged_state_was_set: trace -> string -> principal -> state_id -> bytes -> prop
let tagged_state_was_set tr tag prin sess_id content =
  let full_content = {tag; content;} in
  let full_content_bytes = serialize tagged_state full_content in
  state_was_set tr prin sess_id full_content_bytes

val tagged_state_was_set_grows:
  tr1:trace -> tr2:trace ->
  tag:string -> prin:principal -> sid:state_id -> e:bytes  ->
  Lemma
  (requires tagged_state_was_set tr1 tag prin sid e /\ tr1 <$ tr2)
  (ensures tagged_state_was_set tr2 tag prin sid e)
  [SMTPat (tagged_state_was_set tr1 tag prin sid e); SMTPat (tr1 <$ tr2)]
let tagged_state_was_set_grows tr1 tr2 tag prin sid e =
  reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set);
  ()

(*** API for tagged sessions ***)

[@@ "opaque_to_smt"]
val set_tagged_state: string -> principal -> state_id -> bytes -> traceful unit
let set_tagged_state tag prin sess_id content =
  let full_content = {tag; content;} in
  let full_content_bytes = serialize tagged_state full_content in
  set_state prin sess_id full_content_bytes

[@@ "opaque_to_smt"]
val get_tagged_state: string -> principal -> state_id -> traceful (option bytes)
let get_tagged_state the_tag prin sess_id =
  let*? full_content_bytes = get_state prin sess_id in
  match parse tagged_state full_content_bytes with
    | None -> return None
    | Some ({tag; content;}) ->
      if tag = the_tag then return (Some content)
      else return None

val set_tagged_state_state_was_set:
  tag:string -> 
  prin:principal -> sess_id:state_id -> content:bytes -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = set_tagged_state tag prin sess_id content tr in
    tagged_state_was_set tr_out tag prin sess_id content
  ))
  [SMTPat (set_tagged_state tag prin sess_id content tr);]
let set_tagged_state_state_was_set tag prin sess_id content tr =
  reveal_opaque (`%set_tagged_state) (set_tagged_state);
  reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set)

val set_tagged_state_invariant:
  {|protocol_invariants|} ->
  tag:string -> spred:local_bytes_state_predicate tag ->
  prin:principal -> sess_id:state_id -> content:bytes -> tr:trace ->
  Lemma
  (requires
    spred.pred tr prin sess_id content /\
    trace_invariant tr /\
    has_local_bytes_state_predicate (|tag, spred|)
  )
  (ensures (
    let ((), tr_out) = set_tagged_state tag prin sess_id content tr in
    trace_invariant tr_out
  ))
  [SMTPat (set_tagged_state tag prin sess_id content tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_bytes_state_predicate (|tag, spred|))]
let set_tagged_state_invariant #invs tag spred prin sess_id content tr =
  reveal_opaque (`%has_local_bytes_state_predicate) (has_local_bytes_state_predicate);
  reveal_opaque (`%set_tagged_state) (set_tagged_state);
  let full_content = {tag; content;} in
  local_eq_global_lemma split_local_bytes_state_predicate_params state_pred.pred tag spred (tr, prin, sess_id, serialize _ full_content) tag (tr, prin, sess_id, content)

val get_tagged_state_same_trace:
  tag:string -> 
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = get_tagged_state tag prin sess_id tr in
    tr == tr_out 
  ))
  [SMTPat (get_tagged_state tag prin sess_id tr);]
let get_tagged_state_same_trace tag prin sess_id tr =
  reveal_opaque (`%get_tagged_state) (get_tagged_state)


val get_tagged_state_state_was_set:
  tag:string -> 
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = get_tagged_state tag prin sess_id tr in
    match opt_content with
    | None -> True
    | Some content ->
        tagged_state_was_set tr tag prin sess_id content
  ))
  [SMTPat (get_tagged_state tag prin sess_id tr)]
let get_tagged_state_state_was_set tag prin sess_id tr =
  reveal_opaque (`%get_tagged_state) (get_tagged_state);
  reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set);
  match get_tagged_state tag prin sess_id tr with
  | (None, _) -> ()
  | (Some _, _) -> (
    let (Some full_cont_bytes, _) = get_state prin sess_id tr in
    serialize_parse_inv_lemma #bytes tagged_state full_cont_bytes    
  )

(*** Theorem ***)

val tagged_state_was_set_implies_pred:
  {|protocol_invariants|} -> tr:trace ->
  tag:string -> spred:local_bytes_state_predicate tag ->
  prin:principal -> sess_id:state_id -> content:bytes ->
  Lemma
  (requires
    tagged_state_was_set tr tag prin sess_id content /\
    trace_invariant tr /\
    has_local_bytes_state_predicate (|tag, spred|)
  )
  (ensures spred.pred tr prin sess_id content)
  [SMTPat (tagged_state_was_set tr tag prin sess_id content);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_bytes_state_predicate (|tag, spred|));
  ]
let tagged_state_was_set_implies_pred #invs tr tag spred prin sess_id content =
  reveal_opaque (`%has_local_bytes_state_predicate) (has_local_bytes_state_predicate);
  reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set);
  let full_content = {tag; content;} in
  parse_serialize_inv_lemma #bytes tagged_state full_content;
  let full_content_bytes: bytes = serialize tagged_state full_content in
  local_eq_global_lemma split_local_bytes_state_predicate_params state_pred.pred tag spred (tr, prin, sess_id, full_content_bytes) tag (tr, prin, sess_id, content)
