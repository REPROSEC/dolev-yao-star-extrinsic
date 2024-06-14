module DY.Example.Invariants

open Comparse
open DY.Core
module L = DY.Lib
module List = FStar.List.Tot.Base

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
  let* new_sess_id = new_session_id prin in
  set_state prin new_sess_id (serialize p_state new_state);*
  return new_sess_id


/// one step: send a message and increase the counter by 1
val next: principal -> state_id -> traceful (option unit)
let next prin sid =
  let*? curr_state = get_state prin sid in
  let*? S idn c = return (parse p_state curr_state) in
  send_msg (serialize message (M prin));*
  set_state prin sid (serialize p_state (S idn (c+1)));*
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

val send_msg_no_state:
  msg:bytes -> tr:trace ->
  Lemma 
    ( let (_, tr_out) = send_msg msg tr in 
      forall p sid. no_set_state_entry_for p sid (tr_out `suffix_after` tr)
    )
  [SMTPat (send_msg msg tr)]
let send_msg_no_state msg tr = 
  reveal_opaque (`%send_msg) send_msg;
  reveal_opaque (`%get_state) get_state

// TODO: this proof is slow and unstable
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
  | (Some st_b, _) -> (
      match parse p_state st_b with
      | None -> ()
      | Some (S idn c) -> (          
          let msg = M p in
          let msg_b = serialize message msg in
          let (_, tr_after_msg) = send_msg msg_b tr in

          let next_state = S idn (c+1) in
          let next_state_b = serialize p_state next_state in
          let (_,tr_after_next_state) = set_state p sid next_state_b tr_after_msg in
          

          //assume(trace_invariant tr_after_next_state)

          serialize_wf_lemma message (is_publishable tr) msg;
          // assert(is_publishable tr msg_b);
          // assert(trace_event_invariant tr (MsgSent msg_b ));

          serialize_wf_lemma p_state (is_knowable_by (principal_state_label p sid) tr_after_msg) next_state;
          // assert(state_pred tr_after_msg p sid next_state_b);
          
          //let session_after_msg = get_session p sid tr_after_msg in          
          let session_before_msg = get_session p sid tr in                  
          // assert(tr <$ tr_after_msg);
          assert(no_set_state_entry_for p sid (tr_after_msg `suffix_after` tr));
          assert(session_pred_opt tr session_before_msg p sid next_state_b);
          session_pred_later tr tr_after_msg p sid next_state_b
          // assert(global_state_pred tr_after_msg p sid next_state_b);
          // assert(trace_event_invariant tr_after_msg (SetState p sid next_state_b))       
        )
    )
