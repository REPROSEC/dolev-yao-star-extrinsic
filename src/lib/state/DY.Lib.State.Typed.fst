module DY.Lib.State.Typed

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Tagged

class local_state (a:Type0) = {
  tag: string;
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  format: parseable_serializeable bytes a;
}

val mk_local_state_instance:
  #a:Type0 -> {|parseable_serializeable bytes a|} -> string ->
  local_state a
let mk_local_state_instance #a #format tag = {
  tag;
  format;
}

val typed_state_pred_label_input:
  a:Type0 ->
  Type u#1
let typed_state_pred_label_input a =
  principal -> string -> state_id -> a -> prop

val compile_typed_state_pred_label_input:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  typed_state_pred_label_input a ->
  tagged_state_pred_label_input
let compile_typed_state_pred_label_input #a #ps_a p prin sess_id tag content =
  match parse a content with
  | None -> False
  | Some parsed_content ->
    p prin sess_id tag parsed_content

val typed_state_pred_label:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  typed_state_pred_label_input a ->
  label
let typed_state_pred_label p =
  tagged_state_pred_label (compile_typed_state_pred_label_input p)

val state_was_corrupt:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  trace ->
  principal -> string -> state_id -> a ->
  prop
let state_was_corrupt #a #ps tr prin tag sid content =
  tagged_state_was_corrupt tr prin tag sid (serialize a content)

// This lemma is useful to keep ifuel low
// when reasoning on `typed_state_pred_label`.
val typed_state_pred_label_input_allow_inversion:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  p1:typed_state_pred_label_input a ->
  p2:state_pred_label_input ->
  Lemma
  (inversion (option a))
  [SMTPatOr [
    [SMTPat (state_pred_label_input_can_flow p2 (compile_tagged_state_pred_label_input (compile_typed_state_pred_label_input p1)))];
    [SMTPat (state_pred_label_input_can_flow (compile_tagged_state_pred_label_input (compile_typed_state_pred_label_input p1)) p2)];
  ]]
let typed_state_pred_label_input_allow_inversion #a #ps_a p1 p2 =
  allow_inversion (option a)

val is_corrupt_typed_state_pred_label:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  tr:trace ->
  p:typed_state_pred_label_input a ->
  Lemma (
    typed_state_pred_label p `can_flow tr` public
    <==> (
      exists prin tag sid content.
        state_was_corrupt tr prin tag sid content /\
        p prin tag sid content
    )
  )
  [SMTPat (typed_state_pred_label p `can_flow tr` public)]
let is_corrupt_typed_state_pred_label #a #ps tr p =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (serialize_parse_inv_lemma #bytes a));
  is_corrupt_tagged_state_pred_label tr (compile_typed_state_pred_label_input p)

val principal_typed_state_content_label_input:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  principal -> string -> state_id -> a ->
  typed_state_pred_label_input a
let principal_typed_state_content_label_input #a #ps_a prin1 tag1 sess_id1 content1 =
  fun prin2 tag2 sess_id2 content2 ->
    prin1 == prin2 /\
    tag1 == tag2 /\
    sess_id1 == sess_id2 /\
    content1 == content2

val principal_typed_state_content_label:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  principal -> string -> state_id -> a ->
  label
let principal_typed_state_content_label prin tag sess_id content =
  typed_state_pred_label (principal_typed_state_content_label_input prin tag sess_id content)

noeq
type local_state_predicate {|crypto_invariants|} (a:Type) {|local_state a|} = {
  pred: trace -> principal -> state_id -> a -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:state_id -> content:a ->
    Lemma
    (requires pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id content)
  ;
  pred_knowable:
    tr:trace -> prin:principal -> sess_id:state_id -> content:a ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures is_well_formed _ (is_knowable_by (principal_typed_state_content_label prin (tag #a) sess_id content) tr) content)
  ;
}

noeq
type local_state_update_predicate {|crypto_invariants|} (a:Type) {|local_state a|} = {
  update_pred: trace -> principal -> state_id -> a -> a -> prop;
  update_pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:state_id ->
    content1:a -> content2:a ->
    Lemma
    (requires update_pred tr1 prin sess_id content1 content2 /\ tr1 <$ tr2)
    (ensures update_pred tr2 prin sess_id content1 content2)
  ;
  update_pred_trans:
    tr:trace ->
    prin:principal -> sess_id:state_id ->
    content1:a -> content2:a -> content3:a ->
    Lemma
    (requires
      update_pred tr prin sess_id content1 content2 /\
      update_pred tr prin sess_id content2 content3
    )
    (ensures update_pred tr prin sess_id content1 content3)
  ;
}

val default_local_state_update_pred:
  {|crypto_invariants|} ->
  a:Type -> {|local_state a|} ->
  local_state_update_predicate a
let default_local_state_update_pred #cinvs a #ls_a = {
  update_pred = (fun tr prin sess_id content1 content2 -> True);
  update_pred_later = (fun tr1 tr2 prin sess_id content1 content2 -> ());
  update_pred_trans = (fun tr prin sess_id content1 content2 content3 -> ());
}

val local_state_predicate_to_local_bytes_state_predicate:
  {|crypto_invariants|} ->
  #a:Type -> {|local_state a|} ->
  local_state_predicate a -> local_bytes_state_predicate (tag #a)
let local_state_predicate_to_local_bytes_state_predicate #cinvs #a #ps_a tspred =
  {
    pred = (fun tr prin sess_id content_bytes ->
      match parse a content_bytes with
      | None -> False
      | Some content -> tspred.pred tr prin sess_id content
    );
    pred_later = (fun tr1 tr2 prin sess_id content_bytes ->
      let Some content = parse a content_bytes in
      tspred.pred_later tr1 tr2 prin sess_id content
    );
    pred_knowable = (fun tr prin sess_id content_bytes ->
      let Some content = parse a content_bytes in
      tspred.pred_knowable tr prin sess_id content;
      serialize_parse_inv_lemma a content_bytes;
      serialize_wf_lemma a (is_knowable_by (principal_typed_state_content_label prin (tag #a) sess_id content) tr) content
    );
  }

val local_state_update_predicate_to_local_bytes_state_update_predicate:
  {|crypto_invariants|} ->
  #a:Type -> {|local_state a|} ->
  local_state_update_predicate a -> local_bytes_state_update_predicate (tag #a)
let local_state_update_predicate_to_local_bytes_state_update_predicate #cinvs #a #ps_a tsupred =
  {
    update_pred = (fun tr prin sess_id content_bytes1 content_bytes2 ->
      match (parse a content_bytes1, parse a content_bytes2) with
      | (Some content1, Some content2) -> tsupred.update_pred tr prin sess_id content1 content2
      | _ -> False
    );
    update_pred_later = (fun tr1 tr2 prin sess_id content_bytes1 content_bytes2 ->
      let (Some content1, Some content2) = (parse a content_bytes1, parse a content_bytes2) in
      tsupred.update_pred_later tr1 tr2 prin sess_id content1 content2
    );
    update_pred_trans = (fun tr prin sess_id content_bytes1 content_bytes2 content_bytes3 ->
      let (Some content1, Some content2, Some content3) = (parse a content_bytes1, parse a content_bytes2, parse a content_bytes3) in
      tsupred.update_pred_trans tr prin sess_id content1 content2 content3
    );
  }

val mk_local_state_tag_and_pred:
  #a:Type -> {|local_state a|} ->
  {|crypto_invariants|} -> local_state_predicate a ->
  dtuple2 string local_bytes_state_predicate
let mk_local_state_tag_and_pred #a #ls_a #cinvs spred =
  (|ls_a.tag, (local_state_predicate_to_local_bytes_state_predicate spred)|)

val mk_local_state_tag_and_update_pred:
  #a:Type -> {|local_state a|} ->
  {|crypto_invariants|} -> local_state_update_predicate a ->
  dtuple2 string local_bytes_state_update_predicate
let mk_local_state_tag_and_update_pred #a #ls_a #cinvs supred =
  (|ls_a.tag, (local_state_update_predicate_to_local_bytes_state_update_predicate supred)|)

unfold
val has_local_state_predicate:
  #a:Type -> {|local_state a|} ->
  {|protocol_invariants|} -> local_state_predicate a ->
  prop
let has_local_state_predicate #a #ls #invs spred =
  has_local_bytes_state_predicate (mk_local_state_tag_and_pred spred)

unfold
val has_local_state_update_predicate:
  #a:Type -> {|local_state a|} ->
  {|protocol_invariants|} -> local_state_update_predicate a ->
  prop
let has_local_state_update_predicate #a #ls #invs supred =
  has_local_bytes_state_update_predicate (mk_local_state_tag_and_update_pred supred)

[@@ "opaque_to_smt"]
val state_was_set:
  #a:Type -> {|local_state a|} ->
  trace -> principal -> state_id -> a ->
  prop
let state_was_set #a #ls tr prin sess_id content =
  tagged_state_was_set tr ls.tag prin sess_id (serialize _ content)

[@@ "opaque_to_smt"]
val state_was_set_at:
  #a:Type -> {|local_state a|} ->
  trace -> timestamp -> principal -> state_id -> a ->
  prop
let state_was_set_at #a #ls tr ts prin sess_id content =
  tagged_state_was_set_at tr ts ls.tag prin sess_id (serialize _ content)

val state_was_set_grows:
  #a:Type -> {|local_state a|} ->
  tr1:trace -> tr2:trace ->
  prin:principal -> sid:state_id -> content:a  ->
  Lemma
  (requires state_was_set tr1 prin sid content /\ tr1 <$ tr2)
  (ensures state_was_set tr2 prin sid content)
  [SMTPat (state_was_set tr1 prin sid content); SMTPat (tr1 <$ tr2)]
let state_was_set_grows #a #ls tr1 tr2 prin sid content =
  reveal_opaque (`%state_was_set) (state_was_set #a)

val state_was_set_at_grows:
  #a:Type -> {|local_state a|} ->
  tr1:trace -> tr2:trace -> ts:timestamp ->
  prin:principal -> sid:state_id -> content:a  ->
  Lemma
  (requires state_was_set_at tr1 ts prin sid content /\ tr1 <$ tr2)
  (ensures state_was_set_at tr2 ts prin sid content)
  [SMTPat (state_was_set_at tr1 ts prin sid content); SMTPat (tr1 <$ tr2)]
let state_was_set_at_grows #a #ls tr1 tr2 ts prin sid content =
  reveal_opaque (`%state_was_set_at) (state_was_set_at #a)

[@@ "opaque_to_smt"]
val set_state:
  #a:Type -> {|local_state a|} ->
  principal -> state_id -> a -> traceful unit
let set_state #a #ls prin sess_id content =
  set_tagged_state ls.tag prin sess_id (serialize _ content)

[@@ "opaque_to_smt"]
val get_state:
  #a:Type -> {|local_state a|} ->
  principal -> state_id -> traceful (option a)
let get_state #a #ls prin sess_id =
  let*? content_bytes = get_tagged_state ls.tag prin sess_id in
  match parse a content_bytes with
  | None -> return None
  | Some content -> return (Some content)

[@@ "opaque_to_smt"]
val is_most_recent_state_for:
  #a:Type -> {|local_state a|} ->
  principal -> state_id -> option a -> trace ->
  prop
let is_most_recent_state_for #a #ls_a prin sess_id content_opt tr =
  let (content_opt', _) = get_state prin sess_id tr in
  content_opt == content_opt'

/// Relate most recent typed states with most recent untyped (tagged) states.
val most_recent_tagged_state_most_recent_state_none:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (requires is_most_recent_tagged_state_for ls_a.tag prin sess_id None tr)
  (ensures is_most_recent_state_for #a prin sess_id None tr)
  [SMTPat (is_most_recent_state_for #a #ls_a prin sess_id None tr)]
let most_recent_tagged_state_most_recent_state_none #a #ls_a prin sess_id tr =
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for #a);
  reveal_opaque (`%get_state) (get_state #a);
  ()

val most_recent_tagged_state_most_recent_state_some:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> content:a ->
  tr:trace ->
  Lemma (
    is_most_recent_state_for prin sess_id (Some content) tr <==>
    is_most_recent_tagged_state_for ls_a.tag prin sess_id (Some (serialize a content)) tr
  )
  [SMTPat (is_most_recent_state_for #a #ls_a prin sess_id (Some content) tr)]
let most_recent_tagged_state_most_recent_state_some #a #ls_a prin sess_id content tr =
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for #a);
  reveal_opaque (`%get_state) (get_state #a);
  let content_bytes = serialize a content in
  introduce is_most_recent_state_for prin sess_id (Some content) tr ==>
    is_most_recent_tagged_state_for ls_a.tag prin sess_id (Some content_bytes) tr
  with _. begin
    let (Some tmp, _) = get_tagged_state ls_a.tag prin sess_id tr in
    serialize_parse_inv_lemma #bytes a tmp
  end

/// Connect set_state and get_state with most recent states.
val set_state_is_most_recent_state_for:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> content:a ->
  tr:trace ->
  Lemma (
    let ((), tr_out) = set_state #a prin sess_id content tr in
    is_most_recent_state_for #a prin sess_id (Some content) tr_out
  )
  [SMTPat (set_state #a #ls_a prin sess_id content tr)]
let set_state_is_most_recent_state_for #a #ls_a prin sess_id content tr =
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for #a);
  reveal_opaque (`%set_state) (set_state #a);
  let ((), tr_out) = set_state #a prin sess_id content tr in
  assert(is_most_recent_tagged_state_for ls_a.tag prin sess_id (Some (serialize a content)) tr_out);
  ()

val is_most_recent_state_for_get_state:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> content_opt:option a ->
  tr:trace ->
  Lemma
  (requires is_most_recent_state_for #a #ls_a prin sess_id content_opt tr)
  (ensures (
    let (content_opt', _) = get_state #a #ls_a prin sess_id tr in
    content_opt == content_opt'
  ))
  [SMTPat (is_most_recent_state_for #a #ls_a prin sess_id content_opt tr);
   SMTPat (get_state #a #ls_a prin sess_id tr);
  ]
let is_most_recent_state_for_get_state #a #ls_a prin sess_id content_opt tr =
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for #a)

val get_state_is_most_recent_state_for:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id ->
  tr:trace ->
  Lemma (
    let (content_opt, _) = get_state #a #ls_a prin sess_id tr in
    is_most_recent_state_for #a #ls_a prin sess_id content_opt tr
  )
  [SMTPat (get_state #a #ls_a prin sess_id tr)]
let get_state_is_most_recent_state_for #a #ls_a prin sess_id tr =
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for #a)

/// Using DY.Core.Trace.Modifies, we can pull most recent typed state information forward.
val is_most_recent_state_for_later:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> content_opt:option a ->
  tr1:trace -> tr2:trace ->
  Lemma (requires (
    tr1 <$ tr2 /\
    trace_does_not_modify_addr prin sess_id (tr2 <--> tr1) /\
    is_most_recent_state_for #a #ls_a prin sess_id content_opt tr1
  ))
  (ensures
    is_most_recent_state_for #a #ls_a prin sess_id content_opt tr2
  )
  [SMTPat (tr1 <$ tr2);
   SMTPat (is_most_recent_state_for #a #ls_a prin sess_id content_opt tr2);
   SMTPat (trace_does_not_modify_addr prin sess_id (tr2 <--> tr1));
  ]
let is_most_recent_state_for_later #a #ls_a prin sess_id content_opt tr1 tr2 =
  reveal_opaque (`%is_most_recent_state_for) (is_most_recent_state_for #a);
  reveal_opaque (`%get_state) (get_state #a);
  let (content_bytes_opt1, _) = get_tagged_state ls_a.tag prin sess_id tr1 in
  // The following two assertions trigger `is_most_recent_tagged_state_for_later`.
  // Why is the first one needed when it's in the requires?
  assert(trace_does_not_modify_addr prin sess_id (tr2 <--> tr1));
  assert(is_most_recent_tagged_state_for ls_a.tag prin sess_id content_bytes_opt1 tr2);
  ()

val traceful_is_most_recent_state_for_later:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> content_opt:option a ->
  #b:Type -> f:traceful b -> tr:trace ->
  Lemma (requires (
    traceful_does_not_modify_addr prin sess_id f tr /\
    is_most_recent_state_for #a #ls_a prin sess_id content_opt tr
  ))
  (ensures (
    let (_, tr_out) = f tr in
    is_most_recent_state_for #a #ls_a prin sess_id content_opt tr_out
  ))
  // It's unclear how useful this SMT pattern is, but it at least doesn't seem to hurt.
  [SMTPat (f tr);
   SMTPat (is_most_recent_state_for #a #ls_a prin sess_id content_opt tr);
   SMTPat (traceful_does_not_modify_addr prin sess_id f tr);
  ]
let traceful_is_most_recent_state_for_later #a #ls_a prin sess_id content_opt #b f tr =
  let (_, tr_out) = f tr in
  // Triggers is_most_recent_state_for_later
  assert(trace_does_not_modify_addr prin sess_id (tr_out <--> tr));
  ()

/// Extend the modifies analysis to typed state functions.
val traceful_modifies_set_state:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> content:a -> tr:trace ->
  Lemma (traceful_modifies (set_state #a #ls_a prin sess_id content) tr == FStar.Set.singleton (prin, sess_id))
  [SMTPat (traceful_modifies (set_state #a #ls_a prin sess_id content) tr)]
let traceful_modifies_set_state #a #ls_a prin sess_id content tr =
  reveal_opaque (`%set_state) (set_state #a)

val traceful_modifies_get_state:
  #a:Type -> {|ls_a:local_state a|} ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma (traceful_modifies (get_state #a #ls_a prin sess_id) tr == FStar.Set.empty)
  [SMTPat (traceful_modifies (get_state #a #ls_a prin sess_id) tr)]
let traceful_modifies_get_state #a #ls_a prin sess_id tr =
  reveal_opaque (`%get_state) (get_state #a)


val set_state_state_was_set:
  #a:Type -> {|ls:local_state a|} ->
  prin:principal -> sess_id:state_id -> content:a -> tr:trace ->
  Lemma
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    state_was_set tr_out prin sess_id content
  ))
  [SMTPat (set_state #a #ls prin sess_id content tr);]
let set_state_state_was_set #a #ls  prin sess_id content tr =
  reveal_opaque (`%set_state) (set_state #a);
  reveal_opaque (`%state_was_set) (state_was_set #a #ls)

val set_state_invariant:
  #a:Type -> {|ls:local_state a|} ->
  {|protocol_invariants|} ->
  spred:local_state_predicate a -> supred:local_state_update_predicate a ->
  prin:principal -> sess_id:state_id -> content:a -> tr:trace ->
  Lemma
  (requires
    spred.pred tr prin sess_id content /\
    (
      match get_state prin sess_id tr with
      | (None, _) -> DY.Core.Trace.Base.is_most_recent_state_for prin sess_id None tr
      | (Some old_content, _) -> supred.update_pred tr prin sess_id old_content content
    ) /\
    trace_invariant tr /\
    has_local_state_predicate spred /\
    has_local_state_update_predicate supred
  )
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    trace_invariant tr_out
  ))
  [SMTPat (set_state prin sess_id content tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate spred);
   SMTPat (has_local_state_update_predicate supred);
  ]
let set_state_invariant #a #ls #invs spred supred prin sess_id content tr =
  reveal_opaque (`%set_state) (set_state #a);
  parse_serialize_inv_lemma #bytes a content;
  // Handle update predicate if applicable
  reveal_opaque (`%get_state) (get_state #a);
  ()

val get_state_same_trace:
  #a:Type -> {|ls:local_state a|} ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = get_state #a prin sess_id tr in
    tr == tr_out
  ))
  [SMTPat (get_state #a #ls prin sess_id tr);]
let get_state_same_trace #a #ls prin sess_id tr =
  reveal_opaque (`%get_state) (get_state #a #ls)


val get_state_state_was_set:
  #a:Type -> {|ls:local_state a|} ->
  prin:principal -> sess_id:state_id -> tr:trace ->
  Lemma
  (ensures (
    let (opt_content, tr_out) = get_state #a #ls prin sess_id tr in
    match opt_content with
    | None -> True
    | Some content ->
        state_was_set tr prin sess_id content
  ))
  [SMTPat (get_state #a #ls prin sess_id tr)]
let get_state_state_was_set #a #ls prin sess_id tr =
  reveal_opaque (`%get_state) (get_state #a #ls);
  reveal_opaque (`%state_was_set) (state_was_set #a #ls);
  match get_state #a #ls prin sess_id tr with
  | (None, _) -> ()
  | (Some _, _) ->
      let (Some cont, _) = get_tagged_state ls.tag prin sess_id tr in
      serialize_parse_inv_lemma a cont

val state_was_set_implies_pred:
  #a:Type -> {|local_state a|} ->
  {|protocol_invariants|} -> tr:trace ->
  spred:local_state_predicate a ->
  prin:principal -> sess_id:state_id -> content:a ->
  Lemma
  (requires
    state_was_set tr prin sess_id content /\
    trace_invariant tr /\
    has_local_state_predicate spred
  )
  (ensures spred.pred tr prin sess_id content)
  [SMTPat (state_was_set tr prin sess_id content);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate spred);
  ]
let state_was_set_implies_pred #a #ls #invs tr spred prin sess_id content =
  parse_serialize_inv_lemma #bytes a content;
  reveal_opaque (`%state_was_set) (state_was_set #a)
