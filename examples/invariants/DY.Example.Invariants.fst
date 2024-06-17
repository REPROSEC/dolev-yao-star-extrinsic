module DY.Example.Invariants

open Comparse
open DY.Core
module L = DY.Lib
module List = FStar.List.Tot.Base

#set-options "--fuel 1 --ifuel 1"


/// Experimenting with the new state invariants for sessions and full states

type p_state =
 | S: idn:nat -> ctr: nat -> p_state

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

val new_idn: principal -> traceful nat
let new_idn prin = return 7
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


/// one step: send a message and increase the counter by 1
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
      | Nil -> True // session is empty -> delegate to (single state) pred
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

#push-options "--z3rlimit 25 --z3cliopt 'smt.qi.eager_threshold=100'"
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
          get_session_aux_same p sid tr tr_after_msg1;
          get_session_aux_same p sid tr_after_msg1 tr_after_msg;
          assert(get_session p sid tr_after_msg = get_session p sid tr );

          let next_state = S idn (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_msg in
          serialize_wf_lemma p_state (is_knowable_by (principal_state_label p sid) tr) next_state;
          // assert(trace_invariant tr_after_next_state);

          let ev = E p in
          let ev_b = serialize p_event ev in
          let (_, tr_after_event) = trigger_event p "P" ev_b tr_after_next_state in
          //assert(trace_invariant tr_after_event);

          get_session_aux_same p sid tr_after_next_state tr_after_event;
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
               serialize_wf_lemma p_state (is_knowable_by (principal_state_label p other_sid) tr) other_state;

               set_state_no_set_state_for_others p other_sid other_state_b tr_after_event;
               get_session_aux_same p sid tr_after_event tr_after_other_session;
               // assert(get_session p sid tr_after_other_session = get_session p sid tr_after_next_state);
()
            end
        )
    )
#pop-options
