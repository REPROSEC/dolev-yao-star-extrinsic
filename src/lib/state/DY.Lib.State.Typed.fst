module DY.Lib.State.Typed

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Tagged

class local_version (a:Type0) = {
  tag: string;
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  format: parseable_serializeable bytes a;
}

val mk_local_version_instance:
  #a:Type0 -> {|parseable_serializeable bytes a|} -> string ->
  local_version a
let mk_local_version_instance #a #format tag = {
  tag;
  format;
}

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
  #a:Type -> {|local_version a|} ->
  invs:protocol_invariants -> local_state_predicate a ->
  prop
let has_local_state_predicate #a #ls invs spred =
  has_local_bytes_state_predicate invs (ls.tag, (local_state_predicate_to_local_bytes_state_predicate spred))

[@@ "opaque_to_smt"]
val version_was_set:
  #a:Type -> {|local_version a|} ->
  trace -> principal -> nat -> a ->
  prop
let version_was_set #a #ls tr prin sess_id content =
  tagged_version_was_set tr ls.tag prin sess_id (serialize _ content)

[@@ "opaque_to_smt"]
val set_version:
  #a:Type -> {|local_version a|} ->
  principal -> nat -> a -> traceful unit
let set_version #a #ls prin sess_id content =
  set_tagged_version ls.tag prin sess_id (serialize _ content)

[@@ "opaque_to_smt"]
val get_latest_version:
  #a:Type -> {|local_version a|} ->
  principal -> nat -> traceful (option a)
let get_latest_version #a #ls prin sess_id =
  let*? content_bytes = get_latest_tagged_version ls.tag prin sess_id in
  match parse a content_bytes with
  | None -> return None
  | Some content -> return (Some content)

val set_version_invariant:
  #a:Type -> {|local_version a|} ->
  {|invs:protocol_invariants|} ->
  spred:local_state_predicate a ->
  prin:principal -> sess_id:nat -> content:a -> tr:trace ->
  Lemma
  (requires
    spred.pred tr prin sess_id content /\
    trace_invariant tr /\
    has_local_state_predicate invs spred
  )
  (ensures (
    let ((), tr_out) = set_version prin sess_id content tr in
    trace_invariant tr_out /\
    version_was_set tr_out prin sess_id content
  ))
  [SMTPat (set_version prin sess_id content tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate invs spred)]
let set_version_invariant #a #ls #invs spred prin sess_id content tr =
  reveal_opaque (`%set_version) (set_version #a);
  reveal_opaque (`%version_was_set) (version_was_set #a);
  parse_serialize_inv_lemma #bytes a content

val get_latest_version_invariant:
  #a:Type -> {|local_version a|} ->
  {|invs:protocol_invariants|} ->
  spred:local_state_predicate a ->
  prin:principal -> sess_id:nat -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_local_state_predicate invs spred
  )
  (ensures (
    let (opt_content, tr_out) = get_latest_version prin sess_id tr in
    tr == tr_out /\ (
      match opt_content with
      | None -> True
      | Some content -> (
        spred.pred tr prin sess_id content
      )
    )
  ))
  [SMTPat (get_latest_version #a prin sess_id tr);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate invs spred)]
let get_latest_version_invariant #a #ls #invs spred prin sess_id tr =
  reveal_opaque (`%get_latest_version) (get_latest_version #a)

val version_was_set_implies_pred:
  #a:Type -> {|local_version a|} ->
  invs:protocol_invariants -> tr:trace ->
  spred:local_state_predicate a ->
  prin:principal -> sess_id:nat -> content:a ->
  Lemma
  (requires
    version_was_set tr prin sess_id content /\
    trace_invariant tr /\
    has_local_state_predicate invs spred
  )
  (ensures spred.pred tr prin sess_id content)
  [SMTPat (version_was_set tr prin sess_id content);
   SMTPat (trace_invariant tr);
   SMTPat (has_local_state_predicate invs spred);
  ]
let version_was_set_implies_pred #a #ls invs tr spred prin sess_id content =
  parse_serialize_inv_lemma #bytes a content;
  reveal_opaque (`%version_was_set) (version_was_set #a)
