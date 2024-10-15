module DY.Lib.State.Database

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Typed

#set-options "--fuel 0 --ifuel 0"

/// This module defines a generic database-like state, which allows
/// for storing structured records (analogously to database rows),
/// and searching to find records satisfying some property (analogous
/// to database search queries).
/// Its primary use case is when a protocol needs to maintain some global
/// invariant across a particular kind of data for multiple sessions ---
/// the prototypical example is ensuring that some session identifier is
/// unique, and so no mix-up attacks arise spuriously from reuse of these
/// identifiers.

(*** Database state and invariants ***)

/// Parameters for defining a database.
/// The tag is used to identify a particular kind of database (since we may
/// have multiple used by different levels of protocols in a system), and
/// we also specify the row type, which needs to be able to be serialized
/// as bytes.

class db_types (row_t:Type0) = {
  // TODO maybe these two tags can be merged into one input (and then derived tags created for the db and the row?)
  db_tag: string;
  row_tag: string;
  ps_row_t: parser_serializer bytes row_t;
}

// TODO Probably need to rework to use reverse lists for this to make sense.
#push-options "--ifuel 1"
val list_growsP:
  #a:Type0 ->
  grows_pred:(a -> a -> prop) ->
  l1:list a -> l2:list a ->
  prop
let rec list_growsP #a grows_pred l1 l2 =
  match (l1, l2) with
  | [], _ -> True
  | h1::t1, [] -> False
  | h1::t1, h2::t2 -> grows_pred h1 h2 /\ list_growsP grows_pred t1 t2
#pop-options

noeq type db_predicate {|crypto_invariants|} (row_t:Type0) {|db_t:db_types row_t|} = {
  // TODO: Should the row_pred (and related) take a state ID?
  // In principle, the user shouldn't be interacting with rows directly by state ID anyway
  row_pred: trace -> principal -> row_t -> prop;
  row_pred_later: tr1:trace -> tr2:trace -> prin:principal -> row:row_t -> Lemma
    (requires row_pred tr1 prin row /\ tr1 <$ tr2)
    (ensures row_pred tr2 prin row)
  ;
  row_pred_knowable: tr:trace -> prin:principal -> row:row_t -> Lemma
    (requires row_pred tr prin row)
    (ensures is_well_formed_prefix db_t.ps_row_t (is_knowable_by (principal_label prin) tr) row)
  ;

  // TODO: Should this also take two traces (trace when first state was set, trace now)?
  row_update_pred: trace -> principal -> row_t -> row_t -> prop;

  db_global_pred: trace -> principal -> state_id -> list row_t -> prop;
  db_global_pred_empty: tr:trace -> prin:principal -> sess_id:state_id -> Lemma
    (ensures db_global_pred tr prin sess_id [])
  ;
  db_global_pred_update: tr1:trace -> tr2:trace -> prin:principal -> sess_id:state_id -> db1:list row_t -> db2:list row_t -> Lemma
    (requires db_global_pred tr1 prin sess_id db1 /\
      tr1 <$ tr2 /\
      list_growsP (row_update_pred tr2 prin) db1 db2
    )
    (ensures db_global_pred tr2 prin sess_id db2)
  ;
  // No knowable lemma needed for the overall database, because it holds by construction.
}

/// TODO give actual instances
let ps_state_id : parser_serializer bytes state_id = admit()
let ps_string : parser_serializer bytes string = admit()

instance parseable_serializeable_bytes_db_row (row_t:Type0) {|db_t:db_types row_t|} : parseable_serializeable bytes row_t = mk_parseable_serializeable (db_t.ps_row_t)

instance local_state_db_entry (row_t:Type0) {|db_t:db_types row_t|}: local_state row_t = {
  tag = db_t.row_tag;
  format = (parseable_serializeable_bytes_db_row row_t);
}

/// TODO: Could also make an indirection record type to the state ID, making it easier to add more metadata
[@@ with_bytes bytes]
noeq type db = {
  [@@@ with_parser #bytes (ps_list (ps_state_id))]
  rows: list (state_id)
}

%splice [ps_db] (gen_parser (`db))
%splice [ps_db_is_well_formed] (gen_is_well_formed_lemma (`db))

instance parseable_serializeable_bytes_db : parseable_serializeable bytes db = mk_parseable_serializeable (ps_db)

instance local_state_db (row_t:Type0) {|db_t:db_types row_t|}: local_state db = {
  tag = db_t.db_tag;
  format = (parseable_serializeable_bytes_db);
}

val db_row_session_invariant:
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  local_state_predicate row_t
let db_row_session_invariant #cinvs #row_t #db_t db_pred = {
  pred = (fun tr prin state_id row -> db_pred.row_pred tr prin row);
  pred_later = (fun tr1 tr2 prin state_id row -> db_pred.row_pred_later tr1 tr2 prin row);
  pred_knowable = (fun tr prin state_id row ->
    db_pred.row_pred_knowable tr prin row;
    assert(is_well_formed _ (is_knowable_by (principal_label prin) tr) row);
    assert(principal_label prin `can_flow tr` principal_state_label prin state_id);
//    assert(is_well_formed _ (is_knowable_by (principal_state_label prin state_id) tr) row);
    ()
  );
}


val is_pointer_to_row :
  #row_t:Type0 -> {|db_types row_t|} ->
  tr:trace ->
  prin:principal -> row_state_id:state_id ->
  prop
let is_pointer_to_row #row_t #db_t tr prin row_state_id =
  let (row_opt, _) = get_state #row_t prin row_state_id tr in
  Some? row_opt

val get_row_by_pointer :
  #row_t:Type0 -> {|db_types row_t|} ->
  tr:trace ->
  prin:principal -> row_state_id:state_id{is_pointer_to_row #row_t tr prin row_state_id} ->
  row_t
let get_row_by_pointer #row_t #db_t tr prin row_state_id =
  let (row_opt, _) = get_state #row_t prin row_state_id tr in
  Some?.v row_opt

#push-options "--fuel 1 --ifuel 1"
val list_coerceP :
  #a:Type0 ->
  pred:(a -> prop) ->
  l:list a{for_allP pred l} ->
  list (x:a{pred x})
let rec list_coerceP #a pred l =
  for_allP_eq pred l;
  match l with
  | [] -> []
  | h::t -> h::(list_coerceP pred t)
#pop-options

val db_session_invariant:
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  local_state_predicate db
let db_session_invariant #cinvs #row_t #db_t db_pred = {
  pred = (fun tr prin sess_id db ->
    for_allP (is_pointer_to_row #row_t tr prin) db.rows /\
    (
      let tmp : list (sid:state_id{is_pointer_to_row #row_t tr prin sid}) = list_coerceP (is_pointer_to_row #row_t tr prin) db.rows in
      let rows = List.Tot.map (get_row_by_pointer #row_t tr prin) tmp in
      db_pred.db_global_pred tr prin sess_id rows
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id db ->
    // Problem: If the db_data changes from tr1 to tr2 (via an update to one of the state IDs), then this doesn't follow from db_global_pred_later.
    // db_global_pred_later
    // Do we need to revise what input we have?
    // Do we already need some monotonicity on the individual rows?
    // Idea: monotonicity on rows (specified by some row-evolution predicate).
    //   db_global_pred_later assumes that the rows have only updated according to row-evolution predicate, proves global pred later holds.
    //   Proof relies on saying that the db_data updates from tr1 to tr2 according to this evolution predicate (row-wise), and then using
    //   this to apply db_global_pred_later.
    admit()
  );
  pred_knowable = (fun tr prin sess_id db ->
    // Intuition: apply literal_to_bytes_is_publishable to each element of the list
    admit()
  );
}

#push-options "--fuel 1 --ifuel 1"
val db_invariant_empty :
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  tr:trace ->
  prin:principal -> sess_id:state_id ->
  Lemma
  (requires db_pred.db_global_pred tr prin sess_id [])
  (ensures (
   let empty_db : db = { rows = [] } in
   (db_session_invariant db_pred).pred tr prin sess_id empty_db
  ))
let db_invariant_empty #cinvs #row_t #db_t db_pred tr prin sess_id =
  let tmp = list_coerceP (is_pointer_to_row #row_t tr prin) [] in
  ()
#pop-options

val has_db_invariants:
  #row_t:Type0 -> {|db_types row_t|} ->
  {|protocol_invariants|} -> db_pred:db_predicate row_t -> prop
let has_db_invariants #row_t #db_t #invs db_pred =
  let db_local_state : local_state db = local_state_db row_t in
  has_local_state_predicate (db_session_invariant db_pred) /\
  has_local_state_predicate (db_row_session_invariant #invs.crypto_invs #row_t #db_t db_pred)

(*** Database API ***)

[@@ "opaque_to_smt"]
val initialize_db:
  row_t:Type0 -> {|db_types row_t|} -> prin:principal ->
  traceful state_id
let initialize_db row_t #db_t prin =
  let* sess_id = new_session_id prin in
  let session: db = { rows = [] } in
  let db_local_state : local_state db = local_state_db row_t in
  set_state prin sess_id session;*
  return sess_id

[@@ "opaque_to_smt"]
val add_row:
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal -> sess_id:state_id ->
  row:row_t ->
  traceful (option state_id)
let add_row #row_t #db_t prin sess_id row =
  let db_local_state : local_state db = local_state_db row_t in
  let* row_sess_id = new_session_id prin in
  let*? curr_db = get_state prin sess_id in
  let new_db = { rows = row_sess_id::curr_db.rows } in
  set_state prin row_sess_id row;*
  set_state prin sess_id new_db;*
  return (Some row_sess_id)

[@@ "opaque_to_smt"]
val update_row:
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal -> sess_id:state_id ->
  row_sess_id:state_id -> new_row:row_t ->
  traceful (option unit)
let update_row #row_t #db_t prin sess_id row_sess_id new_row =
  let db_local_state : local_state db = local_state_db row_t in
  set_state prin row_sess_id new_row;*
  return (Some ())

#push-options "--fuel 1 --ifuel 1"
val db_find_aux:
  #row_t:Type0 -> {|db_types row_t|} ->
  query:(row_t -> bool) ->
  prin:principal -> l:list (state_id) ->
  traceful (option (state_id & row_t))
let rec db_find_aux #row_t #db_t query prin l =
  match l with
  | [] -> return None
  | x::xs -> begin
    let*? row = get_state #row_t prin x in
    if query row
    then return (Some (x, row))
    else db_find_aux query prin xs
  end
#pop-options

// Look up a row based on a predicate
[@@ "opaque_to_smt"]
val db_find:
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal -> sess_id:state_id ->
  query:(row_t -> bool) ->
  traceful (option (state_id & row_t))
let db_find #row_t #db_t prin sess_id query =
  let db_local_state : local_state db = local_state_db row_t in
  let*? curr_db = get_state prin sess_id in
  db_find_aux query prin curr_db.rows

// TODO: Constrained find only looking at immutable portion?

#push-options "--fuel 1"
val initialize_db_invariant:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  prin:principal ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_db_invariants db_pred
  )
  (ensures (
    let (_, tr_out) = initialize_db row_t prin tr in
    trace_invariant tr_out
  ))
let initialize_db_invariant #invs #row_t #db_t db_pred prin tr =
  reveal_opaque (`%initialize_db) (initialize_db);
  let (sid, tr_out) = initialize_db row_t prin tr in
  db_pred.db_global_pred_empty tr prin sid;
  db_invariant_empty db_pred tr prin sid;
  ()
#pop-options


#push-options "--fuel 1"
val add_row_invariant:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  prin:principal -> sess_id:state_id ->
  row:row_t ->
  tr:trace ->
  Lemma
  (requires
   db_pred.row_pred tr prin row /\
   trace_invariant tr /\
   has_db_invariants db_pred
  )
  (ensures (
   let (_, tr_out) = add_row prin sess_id row tr in
   trace_invariant tr_out
  ))
let add_row_invariant #invs #row_t #db_t db_pred prin sess_id row tr =
  reveal_opaque (`%add_row) (add_row #row_t #db_t);
  let (_, tr_out) = add_row prin sess_id row tr in
  assume(trace_invariant tr_out);
  ()
#pop-options

#push-options "--fuel 1"
val update_row_invariant:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  prin:principal -> sess_id:state_id ->
  new_row:row_t -> row_sess_id:state_id ->
  tr:trace ->
  Lemma
  (requires
   trace_invariant tr /\
   has_db_invariants db_pred /\
   db_pred.row_pred tr prin new_row /\
   (let (old_row_opt, _) = get_state #row_t prin row_sess_id tr in
     Some? old_row_opt /\
     db_pred.row_update_pred tr prin (Some?.v old_row_opt) new_row
   )
  )
  (ensures (
   let (_, tr_out) = update_row prin sess_id row_sess_id new_row tr in
   trace_invariant tr_out
  ))
let update_row_invariant #invs #row_t #db_t db_pred prin sess_id new_row row_sess_id tr =
  reveal_opaque (`%update_row) (update_row #row_t #db_t);
  let (_, tr_out) = update_row prin sess_id row_sess_id new_row tr in
  assume(trace_invariant tr_out);
  ()
#pop-options

// TODO Strengthen postconditions
// What should we get in the None case?
// Can we say more in the Some case?
// Somehow need to use the global pred
#push-options "--fuel 1"
val db_find_invariant:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  prin:principal -> sess_id:state_id ->
  query:(row_t -> bool) ->
  tr:trace ->
  Lemma
  (requires
   trace_invariant tr /\
   has_db_invariants db_pred
  )
  (ensures (
   let (res_opt, tr_out) = db_find prin sess_id query tr in
   trace_invariant tr_out /\
   (
     match res_opt with
     | None -> True
     | Some (row_sess_id, row) -> (
       db_pred.row_pred tr prin row /\
       query row /\ (
         let tmp = local_state_db row_t in
         let (db_opt, tr_out) = get_state prin sess_id tr in
         Some? db_opt /\
         List.Tot.memP row_sess_id ((Some?.v db_opt).rows)
       )
     )
   )
  ))
let db_find_invariant #invs #row_t #db_t db_pred prin sess_id query tr =
  reveal_opaque (`%db_find) (db_find #row_t #db_t);
  let (res_opt, tr_out) = db_find prin sess_id query tr in
  assume(trace_invariant tr_out);
  match res_opt with
  | None -> ()
  | Some (row_sess_id, row) -> begin
    assume(is_pointer_to_row #row_t tr prin row_sess_id);
    assume(get_row_by_pointer #row_t tr prin row_sess_id == row);
    assert(db_pred.row_pred tr prin row);
    assume(query row);
    let tmp = local_state_db row_t in
    let (db_opt, _) = get_state #db prin sess_id tr in
    let Some db = db_opt in
    assume(List.Tot.memP row_sess_id db.rows);
    ()
  end
#pop-options
