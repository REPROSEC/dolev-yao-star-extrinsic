module DY.Example.Invariants.Uniqueness

open Comparse
open DY.Core
module L = DY.Core.Label
module Lib = DY.Lib
module List = FStar.List.Tot.Base
module Trace = DY.Core.Trace.Type

#set-options "--fuel 1 --ifuel 1"

/// Experimenting with the new state invariants for sessions and full states

type p_state =
 | S: idn:nat -> ctr: nat -> p_state

%splice [ps_p_state] (gen_parser (`p_state))
%splice [ps_p_state_is_well_formed] (gen_is_well_formed_lemma (`p_state))

instance parseable_serializeable_bytes_p_state: parseable_serializeable bytes p_state
 = mk_parseable_serializeable ps_p_state


type message =
  | M: alice:principal -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message
 = mk_parseable_serializeable ps_message

let rec find_max_id_in_session (sess:session_raw) : nat = 
    match sess with
    | Nil -> 0
    | Snoc rest state -> 
        match parse p_state state with
        | None -> find_max_id_in_session rest
        | Some (S id _) -> max id (find_max_id_in_session rest)

let rec find_curr_max_id (st:full_state_raw) : nat = 
    match st with
    | [] -> 0
    | (_,sess)::rest -> max (find_max_id_in_session sess) (find_curr_max_id rest)

val new_idn: principal -> traceful nat
let new_idn prin =
  let* opt_fst = get_full_state prin in
  match opt_fst with
  | None -> return (1 <: nat)
  | Some fst -> return ((find_curr_max_id fst + 1)<:nat)


val init: principal -> traceful state_id
let init prin =
  let* idn = new_idn prin in
  let new_state = S idn 0 in
  let* new_sess_id = set_new_session prin (serialize p_state new_state) in
  return new_sess_id

val next: principal -> state_id -> traceful (option unit)
let next prin sid =
  let*? curr_state = get_state prin sid in
  match parse p_state curr_state with
  | None -> return None
  | Some (S idn c) -> (
         send_msg (serialize message (M prin));*
         set_state prin sid (serialize p_state (S idn (c+1)));*
         return (Some ())
  )

let p_cinvs = {
 usages = default_crypto_usages;
 preds = default_crypto_predicates default_crypto_usages
}

noeq type state_predicate_forall_sessions (cinvs:crypto_invariants) = {
pred: trace -> principal -> state_id -> state_raw -> prop;
  session_pred: trace -> session_raw -> principal -> state_id -> state_raw -> prop; 

/// the idea for the new full_state_pred:
/// often the full_state_pred is of the form:
/// forall_sessions full_st
/// (fun sid_i sess_i ->
///    if sid_i = sid
///    then True // this is a redirect to the session_pred 
///    else
///      match sess_i with
///      | Nil -> True // this is a redirect to the session_pred
///      | Snoc _ last_i -> pred_on last_i and cont
/// )
/// to simplify this, we introduce a new full_state_predicate
/// that hides this form.
/// That is, when writing such a full_state_pred we can already assume
/// that sid_i <> sid and Snoc? sess_i
  full_state_pred: trace -> sid_i:state_id -> sess_i:session_raw{Snoc? sess_i} -> principal -> sid:state_id{sid_i <> sid} -> state_raw -> prop;

  pred_knowable:
    tr:trace ->
    prin:principal -> sess_id:state_id -> content:state_raw ->
    Lemma
    (requires pred tr prin sess_id content)
    (ensures
      is_knowable_by #cinvs (L.principal_state_label prin sess_id) tr content
    )
  ;  
  pred_later:
    tr1:trace -> tr2:trace ->
    prin:principal -> sess_id:state_id -> content:state_raw ->
    Lemma
    (requires tr1 <$ tr2 /\ pred tr1 prin sess_id content)
    (ensures pred tr2 prin sess_id content)
  ;
  session_pred_grows: 
    tr1:trace -> tr2:trace -> 
    sess:session_raw -> prin:principal -> sess_id:state_id -> content:state_raw ->
    Lemma
      (requires
        tr1 <$ tr2 /\ session_pred tr1 sess prin sess_id content
      )
      (ensures
        session_pred tr2 sess prin sess_id content
      )
}

/// translating the new full_state_pred to the more general one
/// implementing the structure from above
val f : {|cinvs: crypto_invariants |} -> state_predicate_forall_sessions cinvs -> state_predicate cinvs
let f #cinvs sp = {
  pred = sp.pred;
  session_pred = sp.session_pred;
  full_state_pred = (fun tr full_st p sid cont ->
    forall_sessions full_st
    (fun sid_i sess_i -> 
      if sid_i = sid || Nil? sess_i
      then True
      else sp.full_state_pred tr sid_i sess_i p sid cont
    )
  );
  pred_knowable = sp.pred_knowable;
  pred_later = sp.pred_later;
  session_pred_grows = sp.session_pred_grows
}
 

let p_state_pred: state_predicate_forall_sessions p_cinvs = {
    pred = (fun tr p sid cont -> is_knowable_by #p_cinvs (principal_state_label p sid) tr cont)
  ; session_pred = (fun tr sess prin sid cont ->
     // within a session the idn should stay the same
     match parse p_state cont with
     | None -> False
     | Some (S the_idn _) -> (
         match sess with
         | Nil -> True
         | Snoc init last -> (
             match parse p_state last with
             | None -> True
             | Some last -> last.idn = the_idn
           )
       )
    )
  ; full_state_pred = (fun tr sid_i sess_i p sid cont -> 
      // across sessions the idn must be different
      match parse p_state cont with
        | None -> False
        | Some (S the_idn _) -> begin
        // using the new full_state_pred
        // we can make use of the fact that
        // sess_i is a Snoc 
        // and we only talk about sid_i <> sid
            let Snoc _ last_i = sess_i in
            match parse p_state last_i with
            | None -> True
            | Some last_i -> last_i.idn <> the_idn
        end
    )
  ; pred_later = (fun t1 t2 p sid cont -> ())
  ; pred_knowable = (fun tr p sid cont -> ())
  ; session_pred_grows = (fun tr1 tr2 sess p sid cont -> ())
}

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = p_cinvs;
  trace_invs = {
    state_pred = f p_state_pred;
    event_pred = (fun tr p sid ev -> True)
  }
}

/// since the new full_state_pred is of the special form,
/// we introduce a convenience function to show such a predicate.
/// This uses the same structure,
/// which means that the proof does not need to replicate this structure again.
///
/// Whan using this method, one as to show the predicate only
/// for sid_i <> sid and Snoc? sess_i
/// without having to write these conditions
let full_state_pred_forall_session_intro
  (full_st: full_state_raw) 
  (sid: state_id)
  (p: (sid_i:state_id{sid_i <> sid}) -> (sess_i:session_raw{Snoc? sess_i}) -> prop)
  (pf: (sid_i:state_id{sid_i <> sid}) -> (sess_i:session_raw{Snoc? sess_i /\ (sid_i, sess_i) `List.mem` full_st})
    -> squash (p sid_i sess_i)
  )
  : squash (forall_sessions full_st
    (fun sid_i sess_i ->
    if sid_i = sid || Nil? sess_i
      then True 
      else p sid_i sess_i
    )
    )
= forall_sessions_intro full_st 
  (fun sid_i sess_i ->
     sid_i <> sid /\ Snoc? sess_i ==> p sid_i sess_i 
  )
  (fun sid_i sess_i ->
    introduce (sid_i, sess_i) `List.mem` full_st /\ sid_i <> sid /\ Snoc? sess_i ==> p sid_i sess_i 
    with _ . pf sid_i sess_i
  )

#push-options "--fuel 2 --z3rlimit 20 --z3cliopt 'smt.qi.eager_threshold=20'"
val next_full_state_pred:
  tr:trace -> p:principal -> sid:state_id ->
  Lemma 
  (requires
       trace_invariant tr
     /\ has_state_for tr p sid
     /\ Some? (parse p_state (access_state tr p sid))
  )
  (ensures (
     let S idn c = Some?.v (parse p_state (access_state tr p sid)) in
     let (_, tr_after_msg) = send_msg (serialize message (M p)) tr in
     let (_, tr_after_next_state) = set_state p sid (serialize p_state (S idn (c+1))) tr_after_msg in

       has_full_state_for tr_after_msg p
     /\ full_state_pred tr_after_msg (access_full_state tr_after_msg p) p sid (serialize p_state (S idn (c+1)))
  ))
let next_full_state_pred tr p sid =
  let oldst_b = access_state tr p sid in
  let S idn c = Some?.v (parse p_state oldst_b) in
  let msg = M p in
  let (_, tr_after_msg) = send_msg (serialize message msg) tr in
  let full_st_b = access_full_state tr_after_msg p in

  // using the new method to proof the full_state_pred
  full_state_pred_forall_session_intro full_st_b sid
    // the property p is exactly the full_state_pred 
    (fun sid_i sess_i -> 
       let Snoc init_i last_i = sess_i in 
       match parse p_state last_i with
       | None -> True
       | Some last_i -> last_i.idn <> idn
    )
    (fun sid_i sess_i -> 
      // in the proof we can make use of:
      // sid_i <> sid
      // Snoc? sess_i
      // and (sid_i, sess_i) `List.mem` full_st_b
       let Snoc _ last_i_b = sess_i in 
       match parse p_state last_i_b with
       | None -> ()
       | Some last_i -> 
           get_state_same p sid_i tr tr_after_msg;    
           full_state_mem_get_session_get_state_forall p tr_after_msg;
           assert(last_i_b = access_state tr_after_msg p sid_i);
           let oldst_entry = SetState p sid oldst_b in
           let tr_after_oldst = tr `suffix_after_event` oldst_entry in
           let last_i_entry = SetState p sid_i last_i_b in
           let tr_after_last_i = tr `suffix_after_event` last_i_entry in

           if tr_after_oldst `has_suffix` tr_after_last_i
           then ( // last_i after oldst on tr
             //admit();
             //get_state_no_set_state_for_on_suffix_after_event tr p sid;
             //no_set_state_entry_for_on_suffix tr_after_oldst tr_after_last_i p sid;
             assert(no_set_state_entry_for p sid tr_after_last_i);
             let tr_before_last_i = tr `prefix_before_event` last_i_entry in
             suff_after_before_event_is_suff_at_event tr last_i_entry;
             no_set_state_entry_for_concat p sid (Snoc Nil last_i_entry) tr_after_last_i;
             get_state_same p sid tr_before_last_i tr;
             assert(oldst_b = access_state tr_before_last_i p sid);
             assert(global_state_pred tr_before_last_i p sid_i last_i_b);
             get_state_appears_in_full_state tr_before_last_i p sid
           )
           else ( // oldst after last_i on tr
             admit();
             suffixes tr tr_after_last_i tr_after_oldst;
             assert(tr_after_last_i `has_suffix` tr_after_oldst);

             get_state_no_set_state_for_on_suffix_after_event tr p sid_i;
             no_set_state_entry_for_on_suffix tr_after_last_i tr_after_oldst p sid_i;
             let tr_before_old = tr `prefix_before_event` oldst_entry in                               
             suff_after_before_event_is_suff_at_event tr oldst_entry;
             no_set_state_entry_for_concat p sid_i (Snoc Nil oldst_entry) tr_after_oldst;
             get_state_same p sid_i tr_before_old tr;
             let state_i_before_old = access_state tr_before_old p sid_i in
             assert(state_i_before_old = last_i_b);
             assert(global_state_pred tr_before_old p sid oldst_b);
             get_state_appears_in_full_state tr_before_old p sid_i  
           )
    )
#pop-options


#push-options "--z3rlimit 25"
val next_invariant: tr:trace -> p:principal -> sid:state_id ->
  Lemma 
    (requires trace_invariant tr)
    (ensures  (
      let (_,tr_out) = next p sid tr in
      trace_invariant tr_out
      )
    )
let next_invariant tr p sid = 
  match get_state p sid tr with
  | (None, _) -> ()
  | (Some oldst_b, _) -> (
      match parse p_state oldst_b with
      | None -> ()
      | Some (S idn c) -> (          
          let msg = M p in
          let msg_b = serialize message msg in
          let (_, tr_after_msg) = send_msg msg_b tr in

          let next_state = S idn (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_msg in
          
          serialize_wf_lemma message (is_publishable tr) msg;

          serialize_wf_lemma p_state (is_knowable_by (principal_state_label p sid) tr_after_msg) next_state;

          get_session_same p sid tr tr_after_msg;

          next_full_state_pred tr p sid
        )
    )
#pop-options
