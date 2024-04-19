module DY.Lib.State.Labeled

open Comparse
open DY.Core
open DY.Lib.SplitPredicate
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

#set-options "--fuel 1 --ifuel 1"

(*** Session predicates ***)

[@@ with_bytes bytes]
type session = {
  [@@@ with_parser #bytes ps_string]
  label: string;
  content: bytes;
}

%splice [ps_session] (gen_parser (`session))
%splice [ps_session_is_well_formed] (gen_is_well_formed_lemma (`session))

instance parseable_serializeable_session: parseable_serializeable bytes session = mk_parseable_serializeable (ps_session)

noeq
type session_pred {|crypto_invariants|} = {
  pred: trace -> principal -> nat -> bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id content)
  ;
  pred_knowable:
    tr:trace -> prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures is_knowable_by (principal_state_label prin sess_id) tr content)
  ;
}

let split_session_pred_func {|crypto_invariants|} : split_predicate_input_values = {
  labeled_data_t = trace & principal & nat & bytes;
  label_t = string;
  encoded_label_t = string;
  raw_data_t = trace & principal & nat & bytes;

  decode_labeled_data = (fun (tr, prin, sess_id, sess_content) -> (
    match parse session sess_content with
    | Some ({label; content}) -> Some (label, (tr, prin, sess_id, content))
    | None -> None
  ));

  encode_label = (fun s -> s);
  encode_label_inj = (fun l1 l2 -> ());

  local_pred = session_pred;
  global_pred = trace -> principal -> nat -> bytes -> prop;

  apply_local_pred = (fun spred (tr, prin, sess_id, content) ->
    spred.pred tr prin sess_id content
  );
  apply_global_pred = (fun spred (tr, prin, sess_id, content) ->
    spred tr prin sess_id content
  );
  mk_global_pred = (fun spred -> fun tr prin sess_id content ->
    spred (tr, prin, sess_id, content)
  );
  apply_mk_global_pred = (fun spred x -> ());
}

val has_session_pred: protocol_invariants -> (string & session_pred) -> prop
let has_session_pred invs (label, spred) =
  has_local_pred split_session_pred_func (state_pred) (label, spred)

(*** Global session predicate builder ***)

val mk_global_session_pred: {|crypto_invariants|} -> list (string & session_pred) -> trace -> principal -> nat -> bytes -> prop
let mk_global_session_pred #cinvs l =
  mk_global_pred split_session_pred_func l

val mk_global_session_pred_correct: invs:protocol_invariants -> lpreds:list (string & session_pred) -> Lemma
  (requires
    invs.trace_invs.state_pred.pred == mk_global_session_pred lpreds /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds)
  )
  (ensures for_allP (has_session_pred invs) lpreds)
let mk_global_session_pred_correct invs lpreds =
  for_allP_eq (has_session_pred invs) lpreds;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_pred_correct split_session_pred_func lpreds))

val mk_global_session_pred_later:
  cinvs:crypto_invariants -> lpreds:list (string & session_pred) ->
  tr1:trace -> tr2:trace -> prin:principal -> sess_id:nat -> full_content:bytes -> Lemma
  (requires mk_global_session_pred lpreds tr1 prin sess_id full_content /\ tr1 <$ tr2)
  (ensures mk_global_session_pred lpreds tr2 prin sess_id full_content)
let mk_global_session_pred_later cinvs lpreds tr1 tr2 prin sess_id full_content =
  mk_global_pred_eq split_session_pred_func lpreds (tr1, prin, sess_id, full_content);
  eliminate exists lab lpred raw_data.
    List.Tot.memP (lab, lpred) lpreds /\
    split_session_pred_func.apply_local_pred lpred raw_data /\
    split_session_pred_func.decode_labeled_data (tr1, prin, sess_id, full_content) == Some (split_session_pred_func.encode_label lab, raw_data)
  returns mk_global_session_pred lpreds tr2 prin sess_id full_content
  with _. (
    let Some (_, (_, _, _, content)) = split_session_pred_func.decode_labeled_data (tr1, prin, sess_id, full_content) in
    lpred.pred_later tr1 tr2 prin sess_id content;
    mk_global_pred_eq split_session_pred_func lpreds (tr2, prin, sess_id, full_content);
    assert(split_session_pred_func.apply_local_pred lpred (tr2, prin, sess_id, content))
  )

val mk_global_session_pred_knowable:
  cinvs:crypto_invariants -> lpreds:list (string & session_pred) ->
  tr:trace -> prin:principal -> sess_id:nat -> full_content:bytes ->
  Lemma
  (requires mk_global_session_pred lpreds tr prin sess_id full_content)
  (ensures is_knowable_by (principal_state_label prin sess_id) tr full_content)
let mk_global_session_pred_knowable cinvs lpreds tr prin sess_id full_content =
  mk_global_pred_eq split_session_pred_func lpreds (tr, prin, sess_id, full_content);
  eliminate exists lab lpred raw_data.
    List.Tot.memP (lab, lpred) lpreds /\
    split_session_pred_func.apply_local_pred lpred raw_data /\
    split_session_pred_func.decode_labeled_data (tr, prin, sess_id, full_content) == Some (split_session_pred_func.encode_label lab, raw_data)
  returns is_knowable_by (principal_state_label prin sess_id) tr full_content
  with _. (
    let Some (label, (_, _, _, content)) = split_session_pred_func.decode_labeled_data (tr, prin, sess_id, full_content) in
    lpred.pred_knowable tr prin sess_id content;
    serialize_parse_inv_lemma session full_content;
    serialize_wf_lemma session (is_knowable_by (principal_state_label prin sess_id) tr) ({label; content})
  )

val mk_state_predicate: cinvs:crypto_invariants -> list (string & session_pred) -> state_predicate cinvs
let mk_state_predicate cinvs lpreds =
  {
    pred = mk_global_session_pred lpreds;
    pred_later = mk_global_session_pred_later cinvs lpreds;
    pred_knowable = mk_global_session_pred_knowable cinvs lpreds;
  }

(*** Predicates on trace ***)

[@@ "opaque_to_smt"]
val labeled_state_was_set: trace -> string -> principal -> nat -> bytes -> prop
let labeled_state_was_set tr label prin sess_id content =
  let full_content = {label; content;} in
  let full_content_bytes = serialize session full_content in
  state_was_set tr prin sess_id full_content_bytes

(*** API for labeled sessions ***)

[@@ "opaque_to_smt"]
val set_labeled_state: string -> principal -> nat -> bytes -> crypto unit
let set_labeled_state label prin sess_id content =
  let* time = get_time in
  let _ = IO.debug_print_string (
      Printf.sprintf "{\"TraceID\": %d, \"Type\": \"Session\", \"SessionID\": %d, \"Tag\": \"%s\", \"Principal\": \"%s\", \"Content\": \"%s\"}\n"
        time sess_id label prin (DY.Core.Printing.bytes_to_string content)
    ) in
  let full_content = {label; content;} in
  let full_content_bytes = serialize session full_content in
  set_state prin sess_id full_content_bytes

[@@ "opaque_to_smt"]
val get_labeled_state: string -> principal -> nat -> crypto (option bytes)
let get_labeled_state lab prin sess_id =
  let*? full_content_bytes = get_state prin sess_id in
  match parse session full_content_bytes with
    | None -> return None
    | Some ({label; content;}) ->
      if label = lab then return (Some content)
      else return None

val set_labeled_state_invariant:
  invs:protocol_invariants ->
  label:string -> spred:session_pred ->
  prin:principal -> sess_id:nat -> content:bytes -> tr:trace ->
  Lemma
  (requires
    spred.pred tr prin sess_id content /\
    trace_invariant tr /\
    has_session_pred invs (label, spred)
  )
  (ensures (
    let ((), tr_out) = set_labeled_state label prin sess_id content tr in
    trace_invariant tr_out /\
    labeled_state_was_set tr_out label prin sess_id content
  ))
  [SMTPat (set_labeled_state label prin sess_id content tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_session_pred invs (label, spred))]
let set_labeled_state_invariant invs label spred prin sess_id content tr =
  reveal_opaque (`%set_labeled_state) (set_labeled_state);
  reveal_opaque (`%labeled_state_was_set) (labeled_state_was_set);
  let full_content = {label; content;} in
  parse_serialize_inv_lemma #bytes session full_content;
  local_eq_global_lemma split_session_pred_func state_pred label spred (tr, prin, sess_id, serialize _ full_content) (tr, prin, sess_id, content)

val get_labeled_state_invariant:
  invs:protocol_invariants ->
  label:string -> spred:session_pred ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_session_pred invs (label, spred)
  )
  (ensures (
    let (opt_content, tr_out) = get_labeled_state label prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> (
        spred.pred tr prin sess_id content
      )
    )
  ))
  [SMTPat (get_labeled_state label prin sess_id tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_session_pred invs (label, spred))]
let get_labeled_state_invariant invs label spred prin sess_id tr =
  reveal_opaque (`%get_labeled_state) (get_labeled_state);
  let (opt_content, tr_out) = get_labeled_state label prin sess_id tr in
  match opt_content with
  | None -> ()
  | Some content ->
    let (Some full_content_bytes, tr) = get_state prin sess_id tr in
    local_eq_global_lemma split_session_pred_func state_pred label spred (tr, prin, sess_id, full_content_bytes) (tr, prin, sess_id, content)

(*** Theorem ***)

val labeled_state_was_set_implies_pred:
  invs:protocol_invariants -> tr:trace ->
  label:string -> spred:session_pred ->
  prin:principal -> sess_id:nat -> content:bytes ->
  Lemma
  (requires
    labeled_state_was_set tr label prin sess_id content /\
    trace_invariant tr /\
    has_session_pred invs (label, spred)
  )
  (ensures spred.pred tr prin sess_id content)
  [SMTPat (labeled_state_was_set tr label prin sess_id content);
   SMTPat (trace_invariant tr);
   SMTPat (has_session_pred invs (label, spred));
  ]
let labeled_state_was_set_implies_pred invs tr label spred prin sess_id content =
  reveal_opaque (`%labeled_state_was_set) (labeled_state_was_set);
  let full_content = {label; content;} in
  parse_serialize_inv_lemma #bytes session full_content;
  let full_content_bytes: bytes = serialize session full_content in
  local_eq_global_lemma split_session_pred_func state_pred label spred (tr, prin, sess_id, full_content_bytes) (tr, prin, sess_id, content)
