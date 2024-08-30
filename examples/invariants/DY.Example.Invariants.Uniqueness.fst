module DY.Example.Invariants.Uniqueness

open Comparse
open DY.Core
module L = DY.Core.Label
module Lib = DY.Lib
module List = FStar.List.Tot.Base

open DY.Example.Invariants.Uniqueness.Identifier

#set-options "--fuel 1 --ifuel 1"

/// Experimenting with the new state invariants for sessions and full states

/// A state type with two identifiers and a counter.
/// The idea is that the identifiers are
/// * the same within a session and
/// * unique across sessions
/// and the counter increases in a session
type p_state =
 | S: idn1:nat -> idn2:nat -> ctr: nat -> p_state

%splice [ps_p_state] (gen_parser (`p_state))
%splice [ps_p_state_is_well_formed] (gen_is_well_formed_lemma (`p_state))

instance parseable_serializeable_bytes_p_state: parseable_serializeable bytes p_state
 = mk_parseable_serializeable ps_p_state

/// some pseudo message and event type
/// (just to test send message and trigger event)

type message =
  | M: alice:principal -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message
 = mk_parseable_serializeable ps_message

type p_event =
  | E: a:principal -> p_event

%splice [ps_p_event] (gen_parser (`p_event))
%splice [ps_p_event_is_well_formed] (gen_is_well_formed_lemma (`p_event))

instance parseable_serializeable_bytes_p_event: parseable_serializeable bytes p_event
 = mk_parseable_serializeable ps_p_event


/// Saying that idn1 and idn2 are supposed to be identifiers of the state
/// with this we can call [compute_new_id] for both of them to generate a fresh identifier
/// and we get the corresponding properties (in particular [new_idn_does_not_appear_in_full_state])
instance has_identifier_p_state_1: has_identifier p_state = {
  base = parseable_serializeable_bytes_p_state;
  to_id = fun state -> state.idn1
}

instance has_identifier_p_state_2: has_identifier p_state = {
  base = parseable_serializeable_bytes_p_state;
  to_id = fun state -> state.idn2
}

val new_idn1: principal -> traceful nat
let new_idn1 prin = 
  compute_new_id #p_state #has_identifier_p_state_1 prin

val new_idn2: principal -> traceful nat
let new_idn2 prin = 
  compute_new_id #p_state #has_identifier_p_state_2 prin


(*** The Protocol ***)

/// a simple initialization step
/// that just generates two new ids and sets the counter to 0
val init: principal -> traceful state_id
let init prin =
  let* idn1 = new_idn1 prin in
  let* idn2 = new_idn2 prin in
  let new_state = S idn1 idn2  0 in
  let* new_sess_id = set_new_session prin (serialize p_state new_state) in
  return new_sess_id


/// a protocol step where
/// * a state is read,
/// * a message is sent
/// * a nonce is generated
/// * a new state is set in the same session with increased counter
/// * an event is triggered
/// * some other state is updated
val next: principal -> state_id -> traceful (option unit)
let next prin sid =
  let*? curr_state = get_state prin sid in
  let*? S idn1 idn2 c = return (parse p_state curr_state) in
  send_msg (serialize message (M prin));*
  let* nonce = mk_rand NoUsage public 7 in
  set_state prin sid (serialize p_state (S idn1 idn2 (c+1)));*
  let ev = E prin in
  trigger_event prin "P" (serialize p_event ev);*

  let other_sid = {the_id = sid.the_id + 1} in
  let*? other_state = get_state prin other_sid in
  let*? S other_idn1 other_idn2 other_c = return (parse p_state other_state) in
  set_state prin other_sid (serialize p_state (S other_idn1 other_idn2 (other_c+1)));*
  return (Some ())


(*** Predicates and Invariants ***)

/// using the default crypto invariants
let p_cinvs = {
 usages = default_crypto_usages;
 preds = default_crypto_predicates default_crypto_usages
}


/// Introducing a specialized instance of [state_predicate].
/// The only difference is in the type of [full_state_pred].
/// 
/// The idea is:
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

noeq type state_predicate_forall_sessions (cinvs:crypto_invariants) = {
  pred: trace -> principal -> state_id -> state_raw -> prop;
  session_pred: trace -> option session_raw -> principal -> state_id -> state_raw -> prop; 
  // notice the new type of the full_state_pred:
  // the full_state_raw argument is replaced by sid_i and sess_i (an element of the full state)
  // with the respective restrictions from above
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
    sess:option session_raw -> prin:principal -> sess_id:state_id -> content:state_raw ->
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
 

(** The state predicates for this Protocol (using the specialized form of full_state_pred) **)

let p_state_pred: state_predicate_forall_sessions p_cinvs = {
    pred = (fun tr p sid cont -> is_knowable_by #p_cinvs (principal_state_label p sid) tr cont)
  ; session_pred = (fun tr sess prin sid cont ->
     // within a session the idns should stay the same
     // and the counter must increase
     match parse p_state cont with
     | None -> False
     | Some (S the_idn1 the_idn2 the_ctr) -> (
         match sess with
         | None -> True
         | Some (Snoc init last) -> (
             match parse p_state last with
             | None -> False //True
             | Some last -> 
                   last.idn1 = the_idn1
                 /\ last.idn2 = the_idn2
                 /\ last.ctr < the_ctr
           )
       )
    )
  ; full_state_pred = (fun tr sid_i sess_i p sid cont -> 
      // across sessions the idns must be different
      match parse p_state cont with
        | None -> False
        | Some (S the_idn1 the_idn2 _) -> begin
        // using the new full_state_pred
        // we can make use of the fact that
        // sess_i is a Snoc 
        // and we only talk about sid_i <> sid
            let Snoc _ last_i = sess_i in
            match parse p_state last_i with
            | None -> False
            | Some last_i -> 
                     last_i.idn1 <> the_idn1
                   /\ last_i.idn2 <> the_idn2
        end
    )
  ; pred_later = (fun t1 t2 p sid cont -> ())
  ; pred_knowable = (fun tr p sid cont -> ())
  ; session_pred_grows = (fun tr1 tr2 sess p sid cont -> ())
}

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = p_cinvs;
  trace_invs = {
    state_pred = f p_state_pred; // translating to the more general state preds
    event_pred = (fun tr p sid ev -> True)
  }
}

/// Since the new full_state_pred is of the special form,
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
  // the property on an element of the full state
  (p: (sid_i:state_id{sid_i <> sid}) -> (sess_i:session_raw{Snoc? sess_i}) -> prop)
  // a proof of the property under our restrictions
  (pf: (sid_i:state_id{sid_i <> sid}) -> (sess_i:session_raw{Snoc? sess_i /\ (sid_i, sess_i) `List.memP` full_st})
    -> squash (p sid_i sess_i)
  )
  :
  // shows the generalized [full_state_pred]
  squash (forall_sessions full_st
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
    introduce (sid_i, sess_i) `List.memP` full_st /\ sid_i <> sid /\ Snoc? sess_i ==> p sid_i sess_i 
    with _ . pf sid_i sess_i
  )
