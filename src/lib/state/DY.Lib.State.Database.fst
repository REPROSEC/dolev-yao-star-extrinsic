module DY.Lib.State.Database

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers
open DY.Lib.State.Typed
open DY.Lib.Event.Typed

#set-options "--fuel 1 --ifuel 1"

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
/// We can abstractly think of any function out of the row type as a column
/// of the database, and we specify the keys of the database, which must be
/// unique and immutable, making searches over them consistent, as a list of
/// such columns (along with their types).

class db_types (row_t:Type0) = {
  // TODO maybe these two tags can be merged into one input (and then derived tags created for the db and the row?)
  db_tag: string;
  row_tag: string;
  ps_row_t: parser_serializer bytes row_t;
  // A key for a row is an eqtype extractable from it.
  // All keys must be unique across rows, and immutable across updates,
  // to ensure consistency of searches by keys.
  keys: list (t:eqtype & (row_t -> t));
}

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

  row_update_pred: trace -> principal -> row_t -> row_t -> prop;
  row_update_pred_later: tr1:trace -> tr2:trace -> prin:principal -> row1:row_t -> row2:row_t -> Lemma
    (requires row_update_pred tr1 prin row1 row2 /\ tr1 <$ tr2)
    (ensures row_update_pred tr2 prin row1 row2)
  ;
  row_update_pred_trans: tr:trace -> prin:principal -> row1:row_t -> row2:row_t -> row3:row_t -> Lemma
    (requires row_update_pred tr prin row1 row2 /\ row_update_pred tr prin row2 row3)
    (ensures row_update_pred tr prin row1 row3)
  ;
}

(*** States and Events for the Database ***)

/// A database consists of two state types --- a tagged version of a row_t, containing individual database entries,
/// and a state containing pointers to all of the rows in the database. This separations allows for row-wise corruption,
/// rather than the whole database having an all-or-nothing corruption model.
///
/// Databases also make use of a db_event to keep track of some of the database invariants. In particular, the fact that
/// a database with unique keys for its rows continues to have unique keys into the future depends on the row update
/// invariant, and so cannot be proven internally to the database invariant. Instead, we set an event when updating the
/// database's table of row pointers, which logs that keys were unique at that point in time, and prove externally that
/// keys continue to be unique in the future (provided that the trace invariants include the row invariants).

instance parseable_serializeable_bytes_db_row (row_t:Type0) {|db_t:db_types row_t|} : parseable_serializeable bytes row_t =
  mk_parseable_serializeable (db_t.ps_row_t)

instance local_state_db_row (row_t:Type0) {|db_t:db_types row_t|}: local_state row_t = {
  tag = db_t.row_tag;
  format = (parseable_serializeable_bytes_db_row row_t);
}

[@@ with_bytes bytes]
type db_event (row_t:Type0) {|db_types row_t|} =
  | DatabaseUpdateEvent:
    db_sess_id:state_id ->
    [@@@ with_parser #bytes (ps_list (ps_state_id))] db_row_pointers:list (state_id) ->
    db_event row_t

%splice [ps_db_event] (gen_parser (`db_event))
%splice [ps_db_event_is_well_formed] (gen_is_well_formed_lemma (`db_event))

instance event_db_event (row_t:Type0) {|db_t:db_types row_t|}: event (db_event row_t) = {
  tag = "DY.Lib.State.Database.Event";
  format = mk_parseable_serializeable (ps_db_event row_t);
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

(*** Database state and event predicates ***)

/// From the db_predicate and db_types, we can construct the predicates for the individual states and
/// events that make up the database. An individual row's predicates can essentially be read directly from
/// the db_predicate, while the database's predicate simply requires that there must be a corresponding event
/// on the trace in order to save a database state with a given set of row pointers.
///
/// The event predicate then contains the information that the database is well-formed, with each row pointer
/// indeed pointing to a row, all of which have unique keys, as specified in db_types.

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

val update_preserves_key:
  #row_t:Type0 -> {|db_types row_t|} ->
  old_row:row_t -> new_row:row_t ->
  key: (t:eqtype & (row_t -> t)) ->
  prop
let update_preserves_key #row_t #db_t old_row new_row key =
  let (|t, get_key|) = key in
  get_key old_row = get_key new_row

unfold
val update_preserves_all_keys:
  #row_t:Type0 -> {|db_types row_t|} ->
  old_row:row_t -> new_row:row_t ->
  prop
let update_preserves_all_keys #row_t #db_t old_row new_row =
  for_allP (update_preserves_key old_row new_row) db_t.keys

val update_preserves_all_keys_trans:
  #row_t:Type0 -> {|db_types row_t|} ->
  row1:row_t -> row2:row_t -> row3:row_t ->
  Lemma
  (requires update_preserves_all_keys row1 row2 /\
            update_preserves_all_keys row2 row3)
  (ensures update_preserves_all_keys row1 row3)
let update_preserves_all_keys_trans #row_t #db_t row1 row2 row3 =
  for_allP_eq (update_preserves_key row1 row2) db_t.keys;
  for_allP_eq (update_preserves_key row2 row3) db_t.keys;
  for_allP_eq (update_preserves_key row1 row3) db_t.keys

val db_row_state_update_invariant:
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  local_state_update_predicate row_t
let db_row_state_update_invariant #cinvs #row_t #db_t db_pred = {
  update_pred = (fun tr prin state_id row1 row2 ->
    db_pred.row_update_pred tr prin row1 row2 /\
    update_preserves_all_keys row1 row2
  );
  update_pred_later = (fun tr1 tr2 prin state_id row1 row2 ->
    db_pred.row_update_pred_later tr1 tr2 prin row1 row2
  );
  update_pred_trans = (fun tr prin state_id row1 row2 row3 ->
    db_pred.row_update_pred_trans tr prin row1 row2 row3;
    update_preserves_all_keys_trans row1 row2 row3
  );
}

/// Idea: Set an event whenever the DB state updates.
/// Use this event to argue that keys *were* unique then,
/// and combine with trace invariant to prove lemma that
/// keys are *always* unique.

val db_session_invariant:
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  local_state_predicate db #(local_state_db row_t)
let db_session_invariant #cinvs #row_t #db_t db_pred = {
  pred = (fun tr prin sess_id db ->
    event_triggered #(db_event row_t) tr prin {db_sess_id=sess_id; db_row_pointers=db.rows}
  );
  pred_later = (fun tr1 tr2 prin sess_id db -> ());
  pred_knowable = (fun tr prin sess_id db_data ->
    let _ : local_state db = local_state_db row_t in
    let knowable_pred = (is_knowable_by (principal_typed_state_content_label prin (DY.Lib.State.Typed.tag #db) sess_id db_data) tr) in
    // Each individual state ID, being a literal, is publishable and so knowable by anyone.
    // knowability of the whole list follows from this.
    for_allP_eq (is_well_formed_prefix ps_state_id knowable_pred) db_data.rows
  );
}

val db_session_update_invariant:
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  local_state_update_predicate db #(local_state_db row_t)
let db_session_update_invariant #cinvs #row_t #db_t db_pred = {
  update_pred = (fun tr prin sess_id db1 db2 ->
    // Does order really matter? Should we be using a set instead?
    squash (List.Tot.Base.strict_suffix_of (db1.rows) (db2.rows))
  );
  update_pred_later = (fun tr1 tr2 prin sess_id db1 db2 -> ());
  update_pred_trans = (fun tr prin sess_id db1 db2 db3 -> ());
}

/// Predicates needed to define the event predicate

val get_row_opt:
  #row_t:Type0 -> {|db_types row_t|} ->
  tr:trace -> prin:principal ->
  ptr:state_id ->
  option row_t
let get_row_opt #row_t #db_t tr prin ptr =
  let (row_opt, _) = get_state #row_t prin ptr tr in
  row_opt

val get_rows:
  #row_t:Type0 -> {|db_types row_t|} ->
  tr:trace -> prin:principal ->
  ptrs:list state_id ->
  list row_t
let get_rows #row_t #db_t tr prin ptrs =
  List.Tot.Base.choose (get_row_opt tr prin) ptrs

val choose_shrinks:
  #a:Type -> #b:Type ->
  f:(a -> option b) ->
  l:list a ->
  Lemma (List.Tot.Base.length (List.Tot.Base.choose f l) <= List.Tot.Base.length l)
let rec choose_shrinks f l =
  match l with
  | [] -> ()
  | x::xs -> choose_shrinks f xs

val unfold_get_rows:
  #row_t:Type0 -> {|db_types row_t|} ->
  tr:trace -> prin:principal ->
  ptrs:list state_id ->
  Lemma
  (requires List.Tot.Base.length ptrs == List.Tot.Base.length (get_rows #row_t tr prin ptrs))
  (ensures (
    match ptrs with
    | [] -> get_rows #row_t tr prin ptrs == []
    | ptr::ptrs' -> (
      Some? (get_row_opt #row_t tr prin ptr) /\
      get_rows tr prin ptrs == (Some?.v (get_row_opt tr prin ptr))::(get_rows #row_t tr prin ptrs')
    )
  ))
let unfold_get_rows #row_t #db_t tr prin ptrs =
  match ptrs with
  | [] -> ()
  | ptr::ptrs' -> choose_shrinks (get_row_opt #row_t tr prin) ptrs'

/// TODO
/// Unfold lemma for get_row_opts
/// guarantee of success if for_allP ...
///
/// What do we actually need?
/// spec: all rows exist (Some for each lookup), and keys unique (property of the list of rows)
/// - could define keys_unique in a variant over options
/// - Or have a way to get rows given knowledge that all exist
///
/// implementation: get all rows that do exist and check for uniqueness
///
/// Could just use a single get_rows function with choose
/// - spec says that this is full-length and keys unique
/// - implementation uses this and checks uniqueness.
/// Enough?

val key_unique:
  #row_t:Type0 -> {|db_types row_t|} ->
  rows_list:list row_t ->
  key: (t:eqtype & (row_t -> t)) ->
  bool
let key_unique #row_t #db_t rows_list key =
  let (|t, get_key|) = key in
  let keys_list = List.Tot.Base.map get_key rows_list in
  List.Tot.Base.noRepeats keys_list

val all_db_keys_unique:
  #row_t:Type0 -> {|db_types row_t|} ->
  rows_list:list row_t ->
  bool
let all_db_keys_unique #row_t #db_t rows_list =
  List.Tot.Base.for_all (key_unique rows_list) db_t.keys

val db_event_predicate:
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  event_predicate (db_event row_t)
let db_event_predicate #cinvs #row_t #db_t db_pred =
  fun tr prin e ->
    (match e with
    | DatabaseUpdateEvent db_sess_id db_row_pointers -> (
      let rows = get_rows #row_t tr prin db_row_pointers in
      List.Tot.Base.length rows == List.Tot.Base.length db_row_pointers /\
      all_db_keys_unique #row_t rows
    ))

unfold
val has_db_state_invariants:
  #row_t:Type0 -> {|db_types row_t|} ->
  {|protocol_invariants|} -> db_pred:db_predicate row_t ->
  prop
let has_db_state_invariants #row_t #db_t #invs db_pred =
  let db_local_state : local_state db = local_state_db row_t in
  has_local_state_predicate (db_session_invariant db_pred) /\
  has_local_state_update_predicate (db_session_update_invariant db_pred) /\
  has_local_state_predicate (db_row_session_invariant db_pred) /\
  has_local_state_update_predicate (db_row_state_update_invariant db_pred)

unfold
val has_db_event_predicate:
  #row_t:Type0 -> {|db_types row_t|} ->
  {|protocol_invariants|} -> db_pred:db_predicate row_t ->
  prop
let has_db_event_predicate #row_t #db_t #invs db_pred =
  has_event_pred (db_event_predicate db_pred)

unfold
val has_db_invariants:
  #row_t:Type0 -> {|db_types row_t|} ->
  {|protocol_invariants|} -> db_pred:db_predicate row_t ->
  prop
let has_db_invariants #row_t #db_t #invs db_pred =
  has_db_state_invariants db_pred /\
  has_db_event_predicate db_pred

(*** Lemmas on the database invariants ***)

/// The following lemmas allow us to extract additional information from the database invariants.
/// For instance, we can ensure that an empty database is always well-formed and that whenever the
/// database predicate holds, all row pointers indeed point to rows, which have unique keys.

val db_event_pred_empty:
  {|crypto_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  tr:trace ->
  prin:principal -> sess_id:state_id ->
  Lemma ((db_event_predicate db_pred) tr prin (DatabaseUpdateEvent sess_id []))
let db_event_pred_empty #cinvs #row_t #db_t db_pred tr prin sess_id =
  List.Tot.Base.for_all_mem (key_unique []) db_t.keys

val key_same_all_rows:
  #row_t:Type0 ->
  rows1:list row_t -> rows2:list row_t ->
  ((t:eqtype & (row_t -> t)) -> prop)
let key_same_all_rows rows1 rows2 =
  (fun (|t, get_key|) -> List.Tot.map get_key rows1 == List.Tot.map get_key rows2)


/// TODO Not currently used
val get_rows_grows:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  tr1:trace -> tr2:trace ->
  prin:principal -> ptrs:list state_id ->
  Lemma
  (requires (
    tr1 <$ tr2 /\
    trace_invariant tr2 /\
    has_db_state_invariants db_pred
  ))
  (ensures (
    let rows1 = get_rows #row_t tr1 prin ptrs in
    let rows2 = get_rows #row_t tr2 prin ptrs in
    List.Tot.Base.length rows1 <= List.Tot.Base.length rows2
  ))
let rec get_rows_grows #invs #row_t #db_t db_pred tr1 tr2 prin ptrs =
  normalize_term_spec (get_rows #row_t tr1 prin ptrs);
  normalize_term_spec (get_rows #row_t tr2 prin ptrs);
  match ptrs with
  | [] -> ()
  | ptr::ptrs' -> (
    get_rows_grows db_pred tr1 tr2 prin ptrs';
    normalize_term_spec (get_rows #row_t tr1 prin ptrs');
    normalize_term_spec (get_rows #row_t tr2 prin ptrs');
    ()
  )

val get_rows_all_keys_same_later:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_t:db_types row_t|} ->
  db_pred:db_predicate row_t ->
  tr1:trace -> tr2:trace ->
  prin:principal -> ptrs:list state_id ->
  Lemma
  (requires (
    List.Tot.Base.length (get_rows #row_t tr1 prin ptrs) == List.Tot.Base.length ptrs /\
    tr1 <$ tr2 /\
    trace_invariant tr2 /\
    has_db_state_invariants db_pred
  ))
  (ensures (
    let rows1 = get_rows #row_t tr1 prin ptrs in
    let rows2 = get_rows #row_t tr2 prin ptrs in
    for_allP (key_same_all_rows rows1 rows2) db_t.keys
  ))
let rec get_rows_all_keys_same_later #invs #row_t #db_t db_pred tr1 tr2 prin ptrs =
  let rows1 = get_rows #row_t tr1 prin ptrs in
  let rows2 = get_rows #row_t tr2 prin ptrs in
  // The following two calls give that rows2 is full-length
  get_rows_grows db_pred tr1 tr2 prin ptrs;
  choose_shrinks (get_row_opt #row_t tr2 prin) ptrs;
  for_allP_eq (key_same_all_rows rows1 rows2) db_t.keys;
  match ptrs with
  | [] -> ()
  | ptr::ptrs' -> (
    unfold_get_rows #row_t tr1 prin ptrs;
    unfold_get_rows #row_t tr2 prin ptrs;
    get_rows_all_keys_same_later db_pred tr1 tr2 prin ptrs';
    let row1::rows1' = rows1 in
    let row2::rows2' = rows2 in
    most_recent_state_update_pred tr2 (db_row_state_update_invariant db_pred) prin ptr row1;
    for_allP_eq (update_preserves_key row1 row2) db_t.keys;
    eliminate row1 == row2 \/ (db_row_state_update_invariant db_pred).update_pred tr2 prin ptr row1 row2
    returns update_preserves_all_keys #row_t #db_t row1 row2
    with _. ()
    and _. (
      // TODO Why is this needed? The proof fails without some normalization here.
      norm_spec [delta_only [`%db_row_state_update_invariant]] (db_row_state_update_invariant db_pred);
      ()
    );
    for_allP_eq (key_same_all_rows rows1' rows2') db_t.keys
  )

val db_event_pred_later:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  tr1:trace -> tr2:trace ->
  prin:principal -> e:db_event row_t ->
  Lemma
  (requires (
    (db_event_predicate db_pred) tr1 prin e /\
    tr1 <$ tr2 /\
    trace_invariant tr2 /\
    has_db_state_invariants db_pred
  ))
  (ensures (
    (db_event_predicate db_pred) tr2 prin e
  ))
let db_event_pred_later #invs #row_t #db_t db_pred tr1 tr2 prin e =
  let rows1 = get_rows #row_t tr1 prin e.db_row_pointers in
  let rows2 = get_rows #row_t tr2 prin e.db_row_pointers in
  let rec tmp_lemma (ptrs:list state_id) :
    Lemma
    (requires List.Tot.Base.length (get_rows #row_t tr1 prin ptrs) == List.Tot.Base.length ptrs)
    (ensures (
      let rows1 = get_rows #row_t tr1 prin ptrs in
      let rows2 = get_rows #row_t tr2 prin ptrs in
      List.Tot.Base.length rows2 == List.Tot.Base.length ptrs /\
      (for_allP (key_same_all_rows rows1 rows2) db_t.keys)
    ))
  = let rows1 = get_rows #row_t tr1 prin ptrs in
    let rows2 = get_rows #row_t tr2 prin ptrs in
    for_allP_eq (key_same_all_rows rows1 rows2) db_t.keys;
    match ptrs with
    | [] -> ()
    | ptr::ptrs' -> (
      unfold_get_rows #row_t tr1 prin ptrs;
      let Some row1 = get_row_opt #row_t tr1 prin ptr in
      let Some row2 = get_row_opt #row_t tr2 prin ptr in
      for_allP_eq (update_preserves_key row1 row2) db_t.keys;

      tmp_lemma ptrs';
      let rows1' = get_rows #row_t tr1 prin ptrs' in
      let rows2' = get_rows #row_t tr2 prin ptrs' in
      for_allP_eq (key_same_all_rows rows1' rows2') db_t.keys;
      for_allP_eq (key_same_all_rows rows1 rows2) db_t.keys;
      ()
    )
  in
  tmp_lemma e.db_row_pointers;
  List.Tot.Base.for_all_mem (key_unique rows1) db_t.keys;
  List.Tot.Base.for_all_mem (key_unique rows2) db_t.keys;
  for_allP_eq (key_same_all_rows rows1 rows2) db_t.keys;
  ()

val db_event_triggered_implies_event_pred:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  tr:trace -> prin:principal -> e:db_event row_t ->
  Lemma
  (requires (
    event_triggered tr prin e /\
    trace_invariant tr /\
    has_db_invariants db_pred
  ))
  (ensures (db_event_predicate db_pred) tr prin e)
  [SMTPat (event_triggered tr prin e);
   SMTPat (trace_invariant tr);
   SMTPat (has_db_invariants db_pred);
  ]
let db_event_triggered_implies_event_pred #invs #row_t #db_t db_pred tr prin e =
  let i = find_event_triggered_at_timestamp tr prin e in
  db_event_pred_later db_pred (prefix tr i) tr prin e

(*** Database API ***)

[@@ "opaque_to_smt"]
val initialize_db:
  row_t:Type0 -> {|db_types row_t|} -> prin:principal ->
  traceful state_id
let initialize_db row_t #db_t prin =
  let* sess_id = new_session_id prin in
  let session: db = { rows = [] } in
  let db_local_state : local_state db = local_state_db row_t in
  trigger_event prin (DatabaseUpdateEvent sess_id [] <: db_event row_t);*
  set_state prin sess_id session;*
  return sess_id

[@@ "opaque_to_smt"]
val add_row:
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal -> sess_id:state_id ->
  row:row_t ->
  traceful (option state_id)
let add_row #row_t #db_t prin sess_id row =
  let*? curr_db = get_state #db #(local_state_db row_t) prin sess_id in
  let* tr = get_trace in
  let old_rows = get_rows tr prin curr_db.rows in
  let* row_sess_id = new_session_id prin in
  // We check before setting the state to ensure that
  // the trace is unchanged if the check fails.
  guard_tr (row_sess_id <> sess_id);*?
  guard_tr (all_db_keys_unique #row_t (row::old_rows));*?
  let new_db = { rows = row_sess_id::curr_db.rows } in
  set_state prin row_sess_id row;*
  trigger_event prin (DatabaseUpdateEvent sess_id new_db.rows <: db_event row_t);*
  set_state #db #(local_state_db row_t) prin sess_id new_db;*
  return (Some row_sess_id)

[@@ "opaque_to_smt"]
val update_row:
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal ->
  row_sess_id:state_id -> new_row:row_t ->
  traceful unit
let update_row #row_t #db_t prin row_sess_id new_row =
  set_state prin row_sess_id new_row

// TODO: Think about how queries should work --- also with keys
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

// Look up a row based on a predicate
[@@ "opaque_to_smt"]
val db_find:
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal -> sess_id:state_id ->
  query:(row_t -> bool) ->
  traceful (option (state_id & row_t))
let db_find #row_t #db_t prin sess_id query =
  let*? curr_db = get_state #db #(local_state_db row_t) prin sess_id in
  db_find_aux query prin curr_db.rows

// TODO: Constrained find only looking at immutable portion?

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
  let (sess_id, tr_sid) = new_session_id prin tr in
  db_event_pred_empty db_pred tr_sid prin sid;
  let (_, tr_ev) = trigger_event prin (DatabaseUpdateEvent sess_id [] <: db_event row_t) tr_sid in
  DY.Core.Trace.Modifies.traceful_is_most_recent_state_for_later prin sess_id None (trigger_event prin ({db_sess_id=sess_id; db_row_pointers=[]} <: db_event row_t)) tr_sid;
  assert(is_most_recent_state_for #db #(local_state_db row_t) prin sess_id None tr_ev);
  ()

val add_row_event_predicate:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  prin:principal ->
  ptr:state_id -> row:row_t ->
  e1:db_event row_t ->
  tr1:trace -> tr2:trace ->
  Lemma
  (requires (
    let rows = get_rows tr1 prin e1.db_row_pointers in
    event_triggered tr1 prin e1 /\
    is_most_recent_state_for #row_t prin ptr (Some row) tr2 /\
    all_db_keys_unique #row_t (row::rows) /\
    trace_invariant tr2 /\
    tr1 <$ tr2 /\
    has_db_invariants db_pred
  ))
  (ensures (
    let e2 = { e1 with db_row_pointers = ptr::e1.db_row_pointers} in
    (db_event_predicate db_pred) tr2 prin e2
  ))
let add_row_event_predicate #invs #row_t #db_t db_pred prin ptr row e1 tr1 tr2 =
  let old_ptrs = e1.db_row_pointers in
  let new_ptrs = ptr::old_ptrs in
  let old_rows1 = get_rows #row_t tr1 prin old_ptrs in
  let old_rows2 = get_rows #row_t tr2 prin old_ptrs in
  let new_rows = get_rows #row_t tr2 prin new_ptrs in
  trace_invariant_before tr1 tr2;
  db_event_triggered_implies_event_pred db_pred tr1 prin e1;
  db_event_triggered_implies_event_pred db_pred tr2 prin e1;
  unfold_get_rows #row_t tr2 prin new_ptrs;
  get_rows_all_keys_same_later db_pred tr1 tr2 prin old_ptrs;
  assert(for_allP (key_same_all_rows old_rows1 old_rows2) db_t.keys);
  for_allP_eq (key_same_all_rows old_rows1 old_rows2) db_t.keys;
  List.Tot.Base.for_all_mem (key_unique new_rows) db_t.keys;
  List.Tot.Base.for_all_mem (key_unique (row::old_rows1)) db_t.keys;
  introduce forall key. List.Tot.Base.memP key db_t.keys ==> key_unique new_rows key
  with introduce _ ==> _ with _. begin
    let (|t, get_key|) = key in
    let old_keys_list1 = List.Tot.Base.map get_key old_rows1 in
    let old_keys_list2 = List.Tot.Base.map get_key old_rows2 in
    let new_keys_list = List.Tot.Base.map get_key new_rows in
    assert(old_keys_list1 == old_keys_list2);
    assert(new_keys_list == (get_key row)::old_keys_list2)
  end;
  assert(all_db_keys_unique new_rows);
  ()

#push-options "--z3cliopt 'smt.qi.eager_threshold=100'"
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
  let (row_sid_opt, tr_out) = add_row prin sess_id row tr in
  match row_sid_opt with
  | None -> assert(tr == tr_out)
  | Some row_sid -> (
    let (Some curr_db, tr') = get_state #db #(local_state_db row_t) prin sess_id tr in
    let old_rows = get_rows tr prin curr_db.rows in
    let (row_sess_id, tr') = new_session_id prin tr' in
    let (_, tr') = guard_tr (all_db_keys_unique #row_t (row::old_rows)) tr' in
    let (_, tr') = guard_tr (row_sess_id <> sess_id) tr' in
    let new_db = { rows = row_sess_id::curr_db.rows } in
    assert(tr == tr');
    assert(is_most_recent_state_for #row_t prin row_sess_id None tr');
    let (_, tr_row_set) = set_state prin row_sess_id row tr' in
    assert(trace_invariant tr_row_set);
    let curr_db_event:db_event row_t = DatabaseUpdateEvent sess_id curr_db.rows in
    let new_db_event:db_event row_t = DatabaseUpdateEvent sess_id new_db.rows in
    add_row_event_predicate db_pred prin row_sess_id row curr_db_event tr tr_row_set;
    let (_, tr_ev) = trigger_event prin new_db_event tr_row_set in
    assert(trace_invariant tr_ev);
    // TODO: This lemma call should ideally be cleaned up. It also is what forces split queries here.
    traceful_is_most_recent_state_for_later #db #(local_state_db row_t) prin sess_id (Some curr_db) (set_state prin row_sess_id row;* trigger_event prin new_db_event) tr;
    assert(is_most_recent_state_for #db #(local_state_db row_t) prin sess_id (Some curr_db) tr_ev);
    assert_norm((db_session_update_invariant db_pred).update_pred tr_ev prin sess_id curr_db new_db);
    let (_, tr_db_set) = set_state #db #(local_state_db row_t) prin sess_id new_db tr_ev in
    assert(trace_invariant tr_db_set);
    assert(tr_out == tr_db_set)
  )
#pop-options

val update_row_invariant:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  db_pred:db_predicate row_t ->
  prin:principal ->
  new_row:row_t -> row_sess_id:state_id ->
  tr:trace ->
  Lemma
  (requires
   trace_invariant tr /\
   has_db_invariants db_pred /\
   db_pred.row_pred tr prin new_row /\
   (match get_state #row_t prin row_sess_id tr with
    | (None, _) -> False
    | (Some old_row, _) -> (
    db_pred.row_update_pred tr prin old_row new_row /\
     update_preserves_all_keys old_row new_row
    )
   )
  )
  (ensures (
   let (_, tr_out) = update_row prin row_sess_id new_row tr in
   trace_invariant tr_out
  ))
let update_row_invariant #invs #row_t #db_t db_pred prin new_row row_sess_id tr =
  reveal_opaque (`%update_row) (update_row #row_t #db_t)

val db_find_aux_preds:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal -> ptrs:list state_id ->
  query:(row_t -> bool) ->
  tr:trace ->
  Lemma
  (requires True)
  (ensures (
    match db_find_aux query prin ptrs tr with
    | (None, tr_out) -> tr == tr_out
    | (Some (row_sess_id, row), tr_out) -> (
      List.Tot.Base.mem row_sess_id ptrs /\
      query row /\
      (get_state #row_t prin row_sess_id tr == (Some row, tr)) /\
      tr == tr_out
    )
  ))
let rec db_find_aux_preds #invs #row_t #db_t prin ptrs query tr =
  match ptrs with
  | [] -> ()
  | ptr::ptrs' -> (
    db_find_aux_preds prin ptrs' query tr;
    match db_find_aux query prin ptrs tr with
    | (None, tr_out) -> ()
    | (Some (row_sess_id, row), tr_out) -> ()
  )

val db_find_same_trace:
  {|protocol_invariants|} ->
  #row_t:Type0 -> {|db_types row_t|} ->
  prin:principal -> sess_id:state_id ->
  query:(row_t -> bool) ->
  tr:trace ->
  Lemma
  (ensures (
    let (_, tr_out) = db_find prin sess_id query tr in
    tr_out == tr
  ))
let db_find_same_trace #invs #row_t #db_t prin sess_id query tr =
  reveal_opaque (`%db_find) (db_find #row_t #db_t);
  match get_state #db #(local_state_db row_t) prin sess_id tr with
  | (None, _) -> ()
  | (Some curr_db, _) -> db_find_aux_preds prin (curr_db.rows) query tr

val is_row_in_db:
  #row_t:Type0 -> {|db_types row_t|} ->
  row:row_t -> row_sess_id:state_id ->
  prin:principal -> db_sess_id:state_id ->
  tr:trace ->
  Type0
let is_row_in_db #row_t #db_t row row_sess_id prin db_sess_id tr =
  match get_state #db #(local_state_db row_t) prin db_sess_id tr with
  | (None, _) -> False
  | (Some curr_db, _) -> (
    List.Tot.Base.mem row_sess_id curr_db.rows /\
    (match get_state #row_t prin row_sess_id tr with
     | (None, _) -> False
     | (Some row', _) -> row == row'
    )
  )


// TODO Strengthen postconditions
// What should we get in the None case?
// Can we say more in the Some case?
// Somehow need to use the global pred
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
   // Add some "row in DB" predicate to capture more of this stuff below
   // row in DB should imply row predicate (always)
   // Using it twice with a key (and/or SID?) matching gives update pred + keys same
   (
     match res_opt with
     | None -> True
     | Some (row_sess_id, row) -> (
       db_pred.row_pred tr prin row /\
       query row /\
       (is_row_in_db row row_sess_id prin sess_id tr) /\
       (
         match get_state #db #(local_state_db row_t) prin sess_id tr with
         | (None, _) -> False
         | (Some db, _) -> List.Tot.Base.mem row_sess_id db.rows
       )
     )
   )
  ))
let db_find_invariant #invs #row_t #db_t db_pred prin sess_id query tr =
  reveal_opaque (`%db_find) (db_find #row_t #db_t);
  let (res_opt, tr_out) = db_find prin sess_id query tr in
  match res_opt with
  | None -> ()
  | Some (row_sess_id, row) -> begin
    let (Some curr_db, tr') = get_state #db #(local_state_db row_t) prin sess_id tr in
    db_find_aux_preds prin curr_db.rows query tr
  end

// What should query do?
// - Row pred, regardless of type of query. Also query holds of row.
// - Option to get just a single row out?
// - Guarantee that row is in DB (somehow)
// - If a row is in the DB at multiple times/tr1 <$ tr2 (how to identify?) then update pred for row
// - unique keys ??? Guarantee that lookups by key always yield the same result?
// - Or just row_in_db_with_key ... twice ==> update pred (and key_same_all_rows?)
