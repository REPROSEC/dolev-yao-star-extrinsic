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

noeq
type local_bytes_state_predicate {|crypto_invariants|} = {
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
    (ensures is_knowable_by (principal_state_label prin sess_id) tr content)
  ;
}

let split_local_bytes_state_predicate_func {|crypto_invariants|} : split_function_input_values = {
  tagged_data_t = trace & principal & state_id & bytes;

  tag_set_t = string;
  tag_t = string;
  is_disjoint = default_disjoint;
  tag_belong_to = (fun dtag tag -> dtag = tag);
  cant_belong_to_disjoint_sets = (fun dtag tag1 tag2 -> ());

  raw_data_t = trace & principal & state_id & bytes;
  output_t = prop;

  default_global_fun = (fun tr prin sess_id sess_content -> False);

  decode_tagged_data = (fun (tr, prin, sess_id, sess_content) -> (
    match parse tagged_state sess_content with
    | Some ({tag; content}) -> Some (tag, (tr, prin, sess_id, content))
    | None -> None
  ));

  local_fun = local_bytes_state_predicate;
  global_fun = trace -> principal -> state_id -> bytes -> prop;

  apply_local_fun = (fun spred (tr, prin, sess_id, content) ->
    spred.pred tr prin sess_id content
  );
  apply_global_fun = (fun spred (tr, prin, sess_id, content) ->
    spred tr prin sess_id content
  );
  mk_global_fun = (fun spred -> fun tr prin sess_id content ->
    spred (tr, prin, sess_id, content)
  );
  apply_mk_global_fun = (fun spred x -> ());
}

val has_local_bytes_state_predicate: protocol_invariants -> (string & local_bytes_state_predicate) -> prop
let has_local_bytes_state_predicate invs (tag, spred) =
  has_local_fun split_local_bytes_state_predicate_func (state_pred) (tag, spred)

(*** Global tagged state predicate builder ***)

val mk_global_local_bytes_state_predicate: {|crypto_invariants|} -> list (string & local_bytes_state_predicate) -> trace -> principal -> state_id -> bytes -> prop
let mk_global_local_bytes_state_predicate #cinvs l =
  mk_global_fun split_local_bytes_state_predicate_func l

val mk_global_local_bytes_state_predicate_correct: invs:protocol_invariants -> lpreds:list (string & local_bytes_state_predicate) -> Lemma
  (requires
    invs.trace_invs.state_pred.pred == mk_global_local_bytes_state_predicate lpreds /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds)
  )
  (ensures for_allP (has_local_bytes_state_predicate invs) lpreds)
let mk_global_local_bytes_state_predicate_correct invs lpreds =
  no_repeats_p_implies_all_disjoint (List.Tot.map fst lpreds);
  for_allP_eq (has_local_bytes_state_predicate invs) lpreds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_local_bytes_state_predicate_func lpreds))

val mk_global_local_bytes_state_predicate_later:
  cinvs:crypto_invariants -> lpreds:list (string & local_bytes_state_predicate) ->
  tr1:trace -> tr2:trace -> prin:principal -> sess_id:state_id -> full_content:bytes -> Lemma
  (requires mk_global_local_bytes_state_predicate lpreds tr1 prin sess_id full_content /\ tr1 <$ tr2)
  (ensures mk_global_local_bytes_state_predicate lpreds tr2 prin sess_id full_content)
let mk_global_local_bytes_state_predicate_later cinvs lpreds tr1 tr2 prin sess_id full_content =
  mk_global_fun_eq split_local_bytes_state_predicate_func lpreds (tr1, prin, sess_id, full_content);
  mk_global_fun_eq split_local_bytes_state_predicate_func lpreds (tr2, prin, sess_id, full_content);
  introduce forall lpred content. split_local_bytes_state_predicate_func.apply_local_fun lpred (tr1, prin, sess_id, content) ==> split_local_bytes_state_predicate_func.apply_local_fun lpred (tr2, prin, sess_id, content) with (
    introduce _ ==> _ with _. lpred.pred_later tr1 tr2 prin sess_id content
  );
  match split_local_bytes_state_predicate_func.decode_tagged_data (tr1, prin, sess_id, full_content) with
  | Some (_, (_, _, _, _)) -> ()
  | None -> ()

val mk_global_local_bytes_state_predicate_knowable:
  cinvs:crypto_invariants -> lpreds:list (string & local_bytes_state_predicate) ->
  tr:trace -> prin:principal -> sess_id:state_id -> full_content:bytes ->
  Lemma
  (requires mk_global_local_bytes_state_predicate lpreds tr prin sess_id full_content)
  (ensures is_knowable_by (principal_state_label prin sess_id) tr full_content)
let mk_global_local_bytes_state_predicate_knowable cinvs lpreds tr prin sess_id full_content =
  mk_global_fun_eq split_local_bytes_state_predicate_func lpreds (tr, prin, sess_id, full_content);
  match split_local_bytes_state_predicate_func.decode_tagged_data (tr, prin, sess_id, full_content) with
  | Some (tag, (_, _, _, content)) -> (
    match find_local_fun split_local_bytes_state_predicate_func lpreds tag with
    | Some lpred -> (
      lpred.pred_knowable tr prin sess_id content;
      serialize_parse_inv_lemma tagged_state full_content;
      serialize_wf_lemma tagged_state (is_knowable_by (principal_state_label prin sess_id) tr) ({tag; content})
    )
    | None -> ()
  )
  | None -> ()

val mk_state_predicate: cinvs:crypto_invariants -> list (string & local_bytes_state_predicate) -> state_predicate cinvs
let mk_state_predicate cinvs lpreds =
  {
    pred = mk_global_local_bytes_state_predicate lpreds;
    pred_later = mk_global_local_bytes_state_predicate_later cinvs lpreds;
    pred_knowable = mk_global_local_bytes_state_predicate_knowable cinvs lpreds;
  }

(*** Predicates on trace ***)

[@@ "opaque_to_smt"]
val tagged_state_was_set: trace -> string -> principal -> state_id -> bytes -> prop
let tagged_state_was_set tr tag prin sess_id content =
  let full_content = {tag; content;} in
  let full_content_bytes = serialize tagged_state full_content in
  state_was_set tr prin sess_id full_content_bytes

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

val set_tagged_state_invariant:
  invs:protocol_invariants ->
  tag:string -> spred:local_bytes_state_predicate ->
  prin:principal -> sess_id:state_id -> content:bytes -> tr:trace ->
  Lemma
  (requires
    spred.pred tr prin sess_id content /\
    trace_invariant tr /\
    has_local_bytes_state_predicate invs (tag, spred)
  )
  (ensures (
    let ((), tr_out) = set_tagged_state tag prin sess_id content tr in
    trace_invariant tr_out /\
    tagged_state_was_set tr_out tag prin sess_id content
  ))
  [SMTPat (set_tagged_state tag prin sess_id content tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_bytes_state_predicate invs (tag, spred))]
let set_tagged_state_invariant invs tag spred prin sess_id content tr =
  reveal_opaque (`%set_tagged_state) (set_tagged_state);
  reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set);
  let full_content = {tag; content;} in
  parse_serialize_inv_lemma #bytes tagged_state full_content;
  local_eq_global_lemma split_local_bytes_state_predicate_func state_pred tag spred (tr, prin, sess_id, serialize _ full_content) tag (tr, prin, sess_id, content)

val get_tagged_state_invariant:
  invs:protocol_invariants ->
  tag:string -> spred:local_bytes_state_predicate ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_local_bytes_state_predicate invs (tag, spred)
  )
  (ensures (
    let (opt_content, tr_out) = get_tagged_state tag prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> (
        spred.pred tr prin sess_id content
      )
    )
  ))
  [SMTPat (get_tagged_state tag prin sess_id tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_bytes_state_predicate invs (tag, spred))]
let get_tagged_state_invariant invs tag spred prin sess_id tr =
  reveal_opaque (`%get_tagged_state) (get_tagged_state);
  let (opt_content, tr_out) = get_tagged_state tag prin sess_id tr in
  match opt_content with
  | None -> ()
  | Some content ->
    let (Some full_content_bytes, tr) = get_state prin sess_id tr in
    local_eq_global_lemma split_local_bytes_state_predicate_func state_pred tag spred (tr, prin, sess_id, full_content_bytes) tag (tr, prin, sess_id, content)

(*** Theorem ***)

val tagged_state_was_set_implies_pred:
  invs:protocol_invariants -> tr:trace ->
  tag:string -> spred:local_bytes_state_predicate ->
  prin:principal -> sess_id:state_id -> content:bytes ->
  Lemma
  (requires
    tagged_state_was_set tr tag prin sess_id content /\
    trace_invariant tr /\
    has_local_bytes_state_predicate invs (tag, spred)
  )
  (ensures spred.pred tr prin sess_id content)
  [SMTPat (tagged_state_was_set tr tag prin sess_id content);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_bytes_state_predicate invs (tag, spred));
  ]
let tagged_state_was_set_implies_pred invs tr tag spred prin sess_id content =
  reveal_opaque (`%tagged_state_was_set) (tagged_state_was_set);
  let full_content = {tag; content;} in
  parse_serialize_inv_lemma #bytes tagged_state full_content;
  let full_content_bytes: bytes = serialize tagged_state full_content in
  local_eq_global_lemma split_local_bytes_state_predicate_func state_pred tag spred (tr, prin, sess_id, full_content_bytes) tag (tr, prin, sess_id, content)
