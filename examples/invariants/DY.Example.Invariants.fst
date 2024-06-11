module DY.Example.Invariants

open Comparse
open DY.Core
module L = DY.Lib

/// Experimenting with the new state invariants for sessions and full states

type p_state =
 | S: idn:nat -> ctr: nat -> p_state

%splice [ps_p_state] (gen_parser (`p_state))
%splice [ps_p_state_is_well_formed] (gen_is_well_formed_lemma (`p_state))

instance parseable_serializeable_bytes_p_state: parseable_serializeable bytes p_state
 = mk_parseable_serializeable ps_p_state

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

val init: principal -> traceful state_id
let init prin =
  let* idn = new_idn prin in
  let new_state = S idn 0 in
  let* new_sess_id = new_session_id prin in
  set_state prin new_sess_id (serialize p_state new_state);*
  return new_sess_id

val next: principal -> state_id -> traceful (option unit)
let next prin sid =
  let*? curr_state = get_state prin sid in
  match parse p_state curr_state with
  | None -> return None
  | Some (S idn c) -> (
         set_state prin sid (serialize p_state (S idn (c+1)));*
         return (Some ())
  )

let p_cinvs = {
 usages = default_crypto_usages;
 preds = default_crypto_predicates default_crypto_usages
}

let p_state_pred: state_predicate p_cinvs = {
    pred = (fun tr p sid cont -> is_knowable_by #p_cinvs (principal_state_label p sid) tr cont)
  ; session_pred = (fun tr sess prin sid cont -> 
      match sess with
      | Nil -> True
      | Snoc init last -> (
          match (parse p_state last, parse p_state cont) with
          | (None,_) -> False
          | (_,None) -> False
          | (Some (S idn ctr), Some (S idn' ctr') ) -> ctr < ctr' 
      )
    )
  ; full_state_pred = (fun tr fst p sid cont -> True)
  ; pred_later = (fun t1 t2 p sid cont -> ())
  ; pred_knowable = (fun tr p sid cont -> ())
}

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = p_cinvs;
  trace_invs = {
    state_pred = p_state_pred;
    event_pred = (fun tr p sid ev -> True)
  }
}


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
          serialize_wf_lemma p_state (is_knowable_by (principal_label p) tr) (S idn (c+1))
    )
    )
