module DY.Lib.State.Typed

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Tagged

(*** Local state typeclass ***)

noeq
type local_state_functional_predicate (a:Type) = {
  pred: a -> prop;
}

class local_state (a:Type0) = {
  tag: string;
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  format: parseable_serializeable bytes a;
  pred: local_state_functional_predicate a;
}

val mk_local_state_instance:
  #a:Type0 -> {|parseable_serializeable bytes a|} ->
  string -> local_state_functional_predicate a ->
  local_state a
let mk_local_state_instance #a #format tag pred = {
  tag;
  format;
  pred;
}

(*** Local state functional predicate ***)

val local_state_functional_predicate_to_local_bytes_state_functional_predicate:
  #a:Type -> {|parseable_serializeable bytes a|} ->
  local_state_functional_predicate a -> local_bytes_state_functional_predicate
let local_state_functional_predicate_to_local_bytes_state_functional_predicate #a #ps_a lpred =
  {
    pred = (fun content_bytes ->
      match parse a content_bytes with
      | None -> False
      | Some content -> lpred.pred content
    );
  }

val has_local_state_functional_predicate:
  #a:Type -> {|local_state a|} ->
  state_functional_predicate -> local_state_functional_predicate a ->
  prop
let has_local_state_functional_predicate #a #ls sfp lpred =
  has_local_bytes_state_functional_predicate sfp (ls.tag, (local_state_functional_predicate_to_local_bytes_state_functional_predicate lpred))

(*** Local state predicate ***)

noeq
type local_state_predicate {|crypto_invariants|} (a:Type) {|parseable_serializeable bytes a|} = {
  pred: trace -> principal -> nat -> a -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:nat -> content:a ->
    Lemma
    (requires pred tr1 prin sess_id content /\ tr1 <$ tr2)
    (ensures pred tr2 prin sess_id content)
  ;
  pred_knowable:
    tr:trace -> prin:principal -> sess_id:nat -> content:a ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures is_well_formed _ (is_knowable_by (principal_state_label prin sess_id) tr) content)
  ;
}

val local_state_predicate_to_local_bytes_state_predicate:
  {|crypto_invariants|} ->
  #a:Type -> {|parseable_serializeable bytes a|} ->
  local_state_predicate a -> local_bytes_state_predicate
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
      serialize_wf_lemma a (is_knowable_by (principal_state_label prin sess_id) tr) content
    );
  }

val has_local_state_predicate:
  #a:Type -> {|local_state a|} ->
  invs:protocol_invariants -> local_state_predicate a ->
  prop
let has_local_state_predicate #a #ls invs spred =
  has_local_bytes_state_predicate invs (ls.tag, (local_state_predicate_to_local_bytes_state_predicate spred))

(*** API for typed state ***)

[@@ "opaque_to_smt"]
val state_was_set:
  #a:Type -> {|local_state a|} ->
  trace -> principal -> nat -> a ->
  prop
let state_was_set #a #ls tr prin sess_id content =
  tagged_state_was_set tr ls.tag prin sess_id (serialize _ content)

[@@ "opaque_to_smt"]
val set_state:
  {|sfp:state_functional_predicate|} ->
  #a:Type -> {|ls:local_state a|} ->
  #squash (has_local_state_functional_predicate sfp ls.pred) ->
  principal -> nat -> x:a{ls.pred.pred x} -> crypto unit
let set_state #sfp #a #ls #pf prin sess_id content =
  set_tagged_state ls.tag (local_state_functional_predicate_to_local_bytes_state_functional_predicate ls.pred) prin sess_id (serialize _ content <: bytes)

[@@ "opaque_to_smt"]
val get_state:
  {|sfp:state_functional_predicate|} ->
  #a:Type -> {|ls:local_state a|} ->
  #squash (has_local_state_functional_predicate sfp ls.pred) ->
  principal -> nat -> crypto (option (x:a{ls.pred.pred x}))
let get_state #sfp #a #ls #pf prin sess_id =
  let*? content_bytes = get_tagged_state ls.tag (local_state_functional_predicate_to_local_bytes_state_functional_predicate ls.pred) prin sess_id in
  let Some content = parse a content_bytes in
  return (Some (content <: content:a{ls.pred.pred content}))

val set_state_invariant:
  #a:Type -> {|ls:local_state a|} ->
  {|invs:protocol_invariants|} ->
  spred:local_state_predicate a ->
  prin:principal -> sess_id:nat -> content:a{ls.pred.pred content} -> tr:trace ->
  Lemma
  (requires
    spred.pred tr prin sess_id content /\
    trace_invariant tr /\
    has_local_state_predicate invs spred /\
    has_local_state_functional_predicate invs.state_inv ls.pred
  )
  (ensures (
    let ((), tr_out) = set_state prin sess_id content tr in
    trace_invariant tr_out /\
    state_was_set tr_out prin sess_id content
  ))
  [SMTPat (set_state prin sess_id content tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate invs spred)]
let set_state_invariant #a #ls #invs spred prin sess_id content tr =
  reveal_opaque (`%set_state) (set_state #_ #a);
  reveal_opaque (`%state_was_set) (state_was_set #a);
  parse_serialize_inv_lemma #bytes a content

val get_state_invariant:
  #a:Type -> {|ls:local_state a|} ->
  {|invs:protocol_invariants|} ->
  spred:local_state_predicate a ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_local_state_predicate invs spred /\
    has_local_state_functional_predicate invs.state_inv ls.pred
  )
  (ensures (
    let (opt_content, tr_out) = get_state prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> (
        spred.pred tr prin sess_id content
      )
    )
  ))
  [SMTPat (get_state #_ #a prin sess_id tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate invs spred)]
let get_state_invariant #a #ls #invs spred prin sess_id tr =
  reveal_opaque (`%get_state) (get_state #_ #a)

val state_was_set_implies_pred:
  #a:Type -> {|local_state a|} ->
  invs:protocol_invariants -> tr:trace ->
  spred:local_state_predicate a ->
  prin:principal -> sess_id:nat -> content:a ->
  Lemma
  (requires
    state_was_set tr prin sess_id content /\
    trace_invariant tr /\
    has_local_state_predicate invs spred
  )
  (ensures spred.pred tr prin sess_id content)
  [SMTPat (state_was_set tr prin sess_id content);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate invs spred);
  ]
let state_was_set_implies_pred #a #ls invs tr spred prin sess_id content =
  parse_serialize_inv_lemma #bytes a content;
  reveal_opaque (`%state_was_set) (state_was_set #a)
