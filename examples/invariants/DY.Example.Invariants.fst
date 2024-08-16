module DY.Example.Invariants

open Comparse
open DY.Core
module L = DY.Lib
module List = FStar.List.Tot.Base

#set-options "--fuel 1 --ifuel 1"


/// Experimenting with the new state invariants for sessions and full states

[@@with_bytes bytes]
type p_state =
 | S: idn:bytes -> ctr: nat -> p_state

%splice [ps_p_state] (gen_parser (`p_state))
%splice [ps_p_state_is_well_formed] (gen_is_well_formed_lemma (`p_state))

instance parseable_serializeable_bytes_p_state: parseable_serializeable bytes p_state
 = mk_parseable_serializeable ps_p_state

[@@with_bytes bytes]
type message =
  | M: nonce:bytes -> message

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


// let max_nat (x:nat) (y:nat) : nat = max x y

// let rec find_max_id_in_session (sess:session_raw) : nat = 
//     match sess with
//     | Nil -> 0
//     | Snoc rest state -> 
//         match parse p_state state with
//         | None -> find_max_id_in_session rest
//         | Some (S id _) -> max_nat id (find_max_id_in_session rest)

// let rec find_curr_max_id (st:full_state_raw) : nat = 
//     match st with
//     | [] -> 0
//     | (_,sess)::rest -> max_nat (find_max_id_in_session sess) (find_curr_max_id rest)

val new_idn: principal -> traceful bytes
let new_idn prin = 
  //return (from_nat 4 7)
  mk_rand NoUsage public 4


// let new_idn prin =
//   let* tr = get_trace in
//   let opt_fst = get_full_state prin tr in
//   match opt_fst with
//   | None -> return (1 <: nat)
//   | Some fst -> return ((find_curr_max_id fst + 1)<:nat)

/// iniitalize a new session with a new identifier and counter 0
val init: principal -> traceful state_id
let init prin =
  let* idn = new_idn prin in
  let new_state = S idn 0 in
  let* new_sess_id = set_new_session prin (serialize p_state new_state)in
  return new_sess_id


/// one step: trying out all trace manipulations there are
/// (read latest state, send messages, set new states, trigger an event)
val next: principal -> state_id -> traceful (option unit)
let next prin sid =
  let*? curr_state = get_state prin sid in
  let*? S idn c = return (parse p_state curr_state) in
  let* nonce = mk_rand NoUsage public 7 in
  send_msg (serialize message (M nonce));*
  send_msg (serialize message (M nonce));*
  set_state prin sid (serialize p_state (S idn (c+1)));*
  let ev = E prin in
  trigger_event prin "P" (serialize p_event ev);*
  
  let other_sid = {the_id = sid.the_id + 1} in
  let*? other_state = get_state prin other_sid in
  let*? S other_idn other_c = return (parse p_state other_state) in
  set_state prin other_sid (serialize p_state (S other_idn (other_c+1)));*
  return (Some ())

let p_cinvs = {
 usages = default_crypto_usages;
 preds = default_crypto_predicates default_crypto_usages
}

/// we only have a session predicate saying that the counter must increase
/// and the identifier must stay the same
let p_state_pred: state_predicate p_cinvs = {
    pred = (fun tr p sid cont -> is_knowable_by #p_cinvs (principal_state_label p sid) tr cont)
  ; session_pred = (fun tr sess prin sid cont -> 
      match sess with
      | Nil -> (
            match parse p_state cont with
            | None -> False
            | Some (S idn ctr) -> 
                   0 < DY.Core.Trace.Type.length tr /\
                   (exists ts. rand_generated_at tr ts idn)
      )
      | Snoc init last -> (
          match (parse p_state last, parse p_state cont) with
          | (None,_) -> False
          | (_,None) -> False
          | (Some (S idn ctr), Some (S idn' ctr') ) -> ctr < ctr' /\ idn = idn'
      )
    )
  ; full_state_pred = (fun tr fst_b p sid cont -> True)
  ; pred_later = (fun t1 t2 p sid cont -> ())
  ; pred_knowable = (fun tr p sid cont -> ())
  ; session_pred_grows = (fun tr1 tr2 sess p sid cont -> ())
}

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = p_cinvs;
  trace_invs = {
    state_pred = p_state_pred;
    event_pred = (fun tr p sid ev -> True)
  }
}

#push-options "--z3rlimit 50 --z3cliopt 'smt.qi.eager_threshold=50'"
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
  | (Some st_b, _) -> (
      match parse p_state st_b with
      | None -> ()
      | Some (S idn c) -> (
          let (nonce, tr_after_rand) = mk_rand NoUsage public 7 tr in
          let msg = M nonce in
          let msg_b = serialize message msg in
          let (_, tr_after_msg1) = send_msg msg_b tr_after_rand in
          let (_, tr_after_msg) = send_msg msg_b tr_after_msg1 in
          
          serialize_wf_lemma message (is_publishable tr_after_rand) msg;
          // assert(trace_invariant tr_after_msg);


          no_set_state_entry_for_suffixes_transitive p sid tr tr_after_rand tr_after_msg1;

          get_session_same p sid tr tr_after_msg1;
          get_session_same p sid tr_after_msg1 tr_after_msg;
          assert(fst (get_session p sid tr_after_msg) = fst (get_session p sid tr) );
          let next_state = S idn (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_msg in
          parse_wf_lemma #bytes p_state #_ (is_knowable_by (principal_state_label p sid) tr) st_b;
          serialize_wf_lemma p_state (is_knowable_by (principal_state_label p sid) tr) next_state;
          // assert(trace_invariant tr_after_next_state);

          let ev = E p in
          let ev_b = serialize p_event ev in
          let (_, tr_after_event) = trigger_event p "P" ev_b tr_after_next_state in
          //assert(trace_invariant tr_after_event);

          get_session_same p sid tr_after_next_state tr_after_event;
          // assert(get_session p sid tr_after_event = get_session p sid tr_after_next_state);

          let other_sid = {the_id = sid.the_id + 1} in
          match get_state p other_sid tr_after_event with
          | (None, _ ) -> ()
          | (Some ost_b, _) -> begin
            match parse p_state ost_b with
            | None -> ()
            | Some (S other_idn other_c) ->
               let other_state = S other_idn (other_c + 1) in
               let other_state_b = serialize p_state other_state in
               let (_, tr_after_other_session) = set_state p other_sid other_state_b tr_after_event in
               parse_wf_lemma #bytes p_state #_ (is_knowable_by (principal_state_label p other_sid) tr_after_event) ost_b;
               serialize_wf_lemma p_state (is_knowable_by (principal_state_label p other_sid) tr_after_event) other_state;

  //             set_state_sets_no_state_for_others p other_sid other_state_b tr_after_event;
               get_session_same p sid tr_after_event tr_after_other_session;
               assert(fst (get_session p sid tr_after_other_session) = fst (get_session p sid tr_after_next_state))
            end
        )
    )
#pop-options


// #push-options "--z3rlimit 25 --z3cliopt 'smt.qi.eager_threshold=100'"
// val session_pred_implies_idn_unique:
//   tr:trace -> p:principal -> sid:state_id -> sid':state_id{sid <> sid'} ->
//   Lemma
//     (requires (
//         trace_invariant tr
//       )
//     )
//   (ensures (
//     let (state, _) = get_state p sid tr in
//     let (state', _) = get_state p sid' tr in
//     match (state, state') with
//     | (None, _ ) -> True
//     | (_, None) -> True
//     | (Some state, Some state') ->
//               match (parse p_state state, parse p_state state') with
//               | (None, _) ->  True
//               | (_, None) -> True
//               | (Some (S idn ctr), Some (S idn' ctr')) -> idn <> idn'
//      )
//   )
// let session_pred_implies_idn_unique tr p sid sid' = 
//     let (state, _) = get_state p sid tr in
//     let (state', _) = get_state p sid' tr in
//     match (state, state') with
//     | (None, _ ) -> ()
//     | (_, None) -> ()
//     | (Some state, Some state') ->
//               match (parse p_state state, parse p_state state') with
//               | (None, _) ->  ()
//               | (_, None) -> ()
//               | (Some (S idn ctr), Some (S idn' ctr')) -> 
                      
//                       let tr_before_state = (prefix_before_event tr (SetState p sid state)) in
//                       assert(global_state_pred #protocol_invariants_p tr_before_state p sid state );
//                       let sess = get_session p sid (prefix_before_event tr (SetState p sid state)) in
//                       assert(session_pred_ #p_cinvs #p_state_pred (prefix_before_event tr (SetState p sid state)) sess p sid state );
//                       get_state_is_last_of_get_session p sid tr_before_state;
//                       assert(exists ts. rand_generated_at tr_before_state ts idn);
//                       admit()

// #pop-options
