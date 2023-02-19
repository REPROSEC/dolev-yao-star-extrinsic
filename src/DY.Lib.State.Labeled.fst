module DY.Lib.State.Labeled

open Comparse
open DY.Core.Label
open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Trace.Invariant
open DY.Core.Trace.Manipulation
open DY.Core.Bytes
open DY.Core.Bytes.Type
open DY.Lib.SplitPredicate
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

#set-options "--fuel 1 --ifuel 1"

(*** Session predicates ***)

type session (bytes:Type0) {|bytes_like bytes|} = {
  [@@@ with_parser #bytes ps_string]
  label: string;
  content: bytes;
}

%splice [ps_session] (gen_parser (`session))
%splice [ps_session_is_well_formed] (gen_is_well_formed_lemma (`session))

instance parseable_serializeable_session (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (session bytes) = mk_parseable_serializeable (ps_session)

let split_session_pred_func: split_predicate_input_values = {
  labeled_data_t = trace & principal & nat & bytes;
  label_t = string;
  encoded_label_t = string;
  raw_data_t = trace & principal & nat & bytes;

  decode_labeled_data = (fun (tr, prin, sess_id, sess_content) -> (
    match parse (session bytes) sess_content with
    | Some ({label; content}) -> Some (label, (tr, prin, sess_id, content))
    | None -> None
  ));

  encode_label = (fun s -> s);
  encode_label_inj = (fun l1 l2 -> ());
}

noeq
type session_pred = {
  pred: crypto_predicates -> trace -> principal -> nat -> bytes -> prop;
  pred_later:
    cpreds:crypto_predicates ->
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires pred cpreds tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred cpreds tr2 prin sess_id content)
  ;
  pred_knowable:
    cpreds:crypto_predicates ->
    tr:trace -> prin:principal -> sess_id:nat -> content:bytes ->
    Lemma
    (requires pred cpreds tr prin sess_id content)
    (ensures is_knowable_by cpreds (principal_state_label prin sess_id) tr content)
  ;
}

val session_pred_to_local_pred:
  crypto_predicates -> session_pred ->
  local_pred split_session_pred_func
let session_pred_to_local_pred cpreds sess_pred (tr, prin, sess_id, content) =
  sess_pred.pred cpreds tr prin sess_id content

val protocol_predicates_to_global_pred: protocol_predicates -> global_pred split_session_pred_func
let protocol_predicates_to_global_pred preds (tr, prin, sess_id, content) =
  preds.trace_preds.state_pred tr prin sess_id content

val has_session_pred: preds:protocol_predicates -> string -> session_pred -> prop
let has_session_pred pr lab spred =
  has_local_pred split_session_pred_func (protocol_predicates_to_global_pred pr) lab (session_pred_to_local_pred pr.crypto_preds spred)

(*** Global session predicate builder ***)

val label_session_pred_to_label_local_pred: cpreds:crypto_predicates -> string & session_pred -> string & local_pred split_session_pred_func
let label_session_pred_to_label_local_pred cpreds (label, spred) =
  (label, session_pred_to_local_pred cpreds spred)

val mk_global_session_pred: cpreds:crypto_predicates -> list (string & session_pred) -> trace -> principal -> nat -> bytes -> prop
let mk_global_session_pred cpreds l tr prin sess_id content =
  mk_global_pred split_session_pred_func (List.Tot.map (label_session_pred_to_label_local_pred cpreds) l) (tr, prin, sess_id, content)

val mk_global_session_pred_correct: preds:protocol_predicates -> lpreds:list (string & session_pred) -> lab:string -> spred:session_pred -> Lemma
  (requires
    preds.trace_preds.state_pred == mk_global_session_pred preds.crypto_preds lpreds /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds) /\
    List.Tot.memP (lab, spred) lpreds
  )
  (ensures has_session_pred preds lab spred)
let mk_global_session_pred_correct preds lpreds lab spred =
  memP_map (label_session_pred_to_label_local_pred preds.crypto_preds) lpreds (lab, spred);
  FStar.Classical.forall_intro_2 (DY.Misc.index_map (label_session_pred_to_label_local_pred preds.crypto_preds));
  FStar.Classical.forall_intro_2 (DY.Misc.index_map (fst #string #(session_pred)));
  FStar.Classical.forall_intro_2 (DY.Misc.index_map (fst #string #(local_pred split_session_pred_func)));
  List.Tot.index_extensionality (List.Tot.map fst lpreds) (List.Tot.map fst (List.Tot.map (label_session_pred_to_label_local_pred preds.crypto_preds) lpreds));
  mk_global_pred_correct split_session_pred_func (List.Tot.map (label_session_pred_to_label_local_pred preds.crypto_preds) lpreds) lab (session_pred_to_local_pred preds.crypto_preds spred)

val mk_global_session_pred_later:
  cpreds:crypto_predicates -> lpreds:list (string & session_pred) ->
  tr1:trace -> tr2:trace -> prin:principal -> sess_id:nat -> content:bytes -> Lemma
  (requires mk_global_session_pred cpreds lpreds tr1 prin sess_id content /\ tr1 <$ tr2)
  (ensures mk_global_session_pred cpreds lpreds tr2 prin sess_id content)
let rec mk_global_session_pred_later cpreds lpreds tr1 tr2 prin sess_id content =
  match lpreds with
  | [] -> ()
  | (_, lpred)::tpreds ->
    FStar.Classical.move_requires (mk_global_session_pred_later cpreds tpreds tr1 tr2 prin sess_id) content;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (lpred.pred_later cpreds tr1 tr2 prin sess_id));
    // Why F*, why???
    match parse (session bytes) content with
    | None -> ()
    | Some _ -> ()

val mk_global_session_pred_knowable:
  cpreds:crypto_predicates -> lpreds:list (string & session_pred) ->
  tr:trace -> prin:principal -> sess_id:nat -> full_content:bytes ->
  Lemma
  (requires mk_global_session_pred cpreds lpreds tr prin sess_id full_content)
  (ensures is_knowable_by cpreds (principal_state_label prin sess_id) tr full_content)
let rec mk_global_session_pred_knowable cpreds lpreds tr prin sess_id full_content =
  match lpreds with
  | [] -> ()
  | (current_label, current_lpred)::tpreds ->
    FStar.Classical.move_requires (mk_global_session_pred_knowable cpreds tpreds tr prin sess_id) full_content;
    match parse (session bytes) full_content with
    | None -> ()
    | Some ({label; content}) -> (
      if label = current_label then (
        introduce current_lpred.pred cpreds tr prin sess_id content ==> is_knowable_by cpreds (principal_state_label prin sess_id) tr full_content
        with _. (
          current_lpred.pred_knowable cpreds tr prin sess_id content;
          serialize_parse_inv_lemma (session bytes) full_content;
          serialize_wf_lemma (session bytes) (is_knowable_by cpreds (principal_state_label prin sess_id) tr) ({label; content})
        )
      ) else ()
    )

(*** API for labeled sessions ***)

val set_labeled_state: string -> principal -> nat -> bytes -> crypto unit
let set_labeled_state lab prin sess_id content =
  let full_content = {
    label = lab;
    content;
  } in
  let full_content_bytes = serialize (session bytes) full_content in
  set_state prin sess_id full_content_bytes

val get_labeled_state: string -> principal -> nat -> crypto (option bytes)
let get_labeled_state lab prin sess_id =
  let*? full_content_bytes = get_state prin sess_id in
  match parse (session bytes) full_content_bytes with
    | None -> return None
    | Some ({label; content;}) ->
      if label = lab then return (Some content)
      else return None

val set_labeled_state_invariant:
  preds:protocol_predicates ->
  label:string -> spred:session_pred ->
  prin:principal -> sess_id:nat -> content:bytes -> tr:trace ->
  Lemma
  (requires
    spred.pred preds.crypto_preds tr prin sess_id content /\
    trace_invariant preds tr /\
    has_session_pred preds label spred
  )
  (ensures (
    let ((), tr_out) = set_labeled_state label prin sess_id content tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (set_labeled_state label prin sess_id content tr);
   SMTPat (trace_invariant preds tr);
   SMTPat (has_session_pred preds label spred)]
let set_labeled_state_invariant preds lab spred prin sess_id content tr =
  assert_norm (forall tr prin sess_id session. protocol_predicates_to_global_pred preds (tr, prin, sess_id, session) <==> preds.trace_preds.state_pred tr prin sess_id session);
  let full_content = {
    label = lab;
    content;
  } in
  parse_serialize_inv_lemma #bytes (session bytes) full_content

val get_labeled_state_invariant:
  preds:protocol_predicates ->
  label:string -> spred:session_pred ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_session_pred preds label spred
  )
  (ensures (
    let (opt_content, tr_out) = get_labeled_state label prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> (
        spred.pred preds.crypto_preds tr prin sess_id content
      )
    )
  ))
  [SMTPat (get_labeled_state label prin sess_id tr);
   SMTPat (trace_invariant preds tr);
   SMTPat (has_session_pred preds label spred)]
let get_labeled_state_invariant preds lab spred prin sess_id tr =
  assert_norm (forall tr prin sess_id session. protocol_predicates_to_global_pred preds (tr, prin, sess_id, session) <==> preds.trace_preds.state_pred tr prin sess_id session)
