module DY.Example.Invariants.Uniqueness

open Comparse
open DY.Core
module L = DY.Lib
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



let p_state_pred: state_predicate p_cinvs = {
    pred = (fun tr p sid cont -> is_knowable_by #p_cinvs (principal_state_label p sid) tr cont)
  ; session_pred = (fun tr sess prin sid cont ->
     True
    )
  ; full_state_pred = (fun tr full_st_b p sid cont -> 
      match parse p_state cont with
        | None -> False
        | Some (S the_idn _) -> begin     
            forall_sessions full_st_b
            (fun sid_i sess_i -> 
              match sess_i with
              | Nil -> True            
                     // this should always be true (and we should hide it from the user)
                     // since this corresponds to [session_pred]
                     // one could also argue that empty sessions should not appear in the full state 
              | Snoc init_i last_i -> begin
                    match parse p_state last_i with
                    | None -> True
                    | Some last_i ->
                        if sid_i = sid // if the new state is added to session sid_i
                          then last_i.idn = the_idn // the id should stay the same within session sid_i
                          else last_i.idn <> the_idn // otherwise the id must be different
                end
            )
        end
    )
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

#push-options "--fuel 2 --z3rlimit 50 --z3cliopt 'smt.qi.eager_threshold=100'"
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

  let next_state = S idn (c+1) in
  let (_,tr_after_next_state) = set_state p sid (serialize p_state next_state) tr_after_msg in

  let full_st_b = access_full_state tr_after_msg p in
  forall_sessions_intro full_st_b
    (fun sid_i sess_i -> 
       match sess_i with
       | Nil -> True
       | Snoc init_i last_i -> (
           match parse p_state last_i with
           | None -> True
           | Some last_i ->
               if sid_i = sid 
                 then last_i.idn = idn
                 else last_i.idn <> idn
         )
    )
    (fun sid_i sess_i _ ->
       match sess_i with
       | Nil -> ()
       | Snoc init_i last_i_b ->
            match parse p_state last_i_b with
            | None -> ()
            | Some last_i -> 
                get_state_same p sid_i tr tr_after_msg;    
                full_state_mem_get_session_get_state_forall p tr_after_msg;
                assert(last_i_b = access_state tr_after_msg p sid_i);
                if sid_i = sid
                then assert(last_i = S idn c)
                else (
                  let oldst_entry = SetState p sid oldst_b in
                  let tr_after_oldst = tr `suffix_after_event` oldst_entry in
                  let last_i_entry = SetState p sid_i last_i_b in
                  let tr_after_last_i = tr `suffix_after_event` last_i_entry in

                  if tr_after_oldst `has_suffix` tr_after_last_i
                  then ( // last_i after oldst on tr
                    //admit();
                    get_state_no_set_state_for_on_suffix_after_event tr p sid;
                    no_set_state_entry_for_on_suffix tr_after_oldst tr_after_last_i p sid;
                    assert(no_set_state_entry_for p sid tr_after_last_i);
                    let tr_before_last_i = tr `prefix_before_event` (SetState p sid_i last_i_b) in
                    suff_after_before_event_is_suff_at_event tr last_i_entry;
                    no_set_state_entry_for_concat p sid (Snoc Nil (SetState p sid_i last_i_b)) tr_after_last_i;
                    get_state_same p sid tr_before_last_i tr;
                    assert(oldst_b = access_state tr_before_last_i p sid);
                    assert(global_state_pred tr_before_last_i p sid_i last_i_b);
                    get_state_appears_in_full_state tr_before_last_i p sid
                  )
                  else ( // oldst after last_i on tr
                    // admit();
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

          next_full_state_pred tr p sid
        )
    )
#pop-options
