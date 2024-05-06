module DY.Example.DH.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Total
open DY.Example.DH.Protocol.Total.Proof
open DY.Example.DH.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

/// The (local) state predicate.

val is_dh_shared_key: trace -> principal -> principal -> bytes -> prop
let is_dh_shared_key tr a b k = exists si sj.
  is_secret (join (principal_state_label a si) (principal_state_label b sj)) tr k /\ 
  get_usage k == AeadKey "DH.aead_key"

let dh_session_pred: typed_session_pred dh_session = {
  pred = (fun tr prin sess_id st ->
    match st with
    | InitiatorSentMsg1 bob x -> (
      let alice = prin in
      is_secret (principal_state_label alice sess_id) tr x /\
      get_usage x == DhKey "DH.dh_key" /\
      event_triggered tr alice (Initiate1 alice bob x)
    )
    | ResponderSentMsg2 alice gx gy y -> (
      let bob = prin in
      is_publishable tr gx /\ is_publishable tr gy /\
      is_knowable_by (principal_state_label bob sess_id) tr y /\
      is_secret (principal_state_label bob sess_id) tr y /\ get_usage y  == DhKey "DH.dh_key" /\
      gy == dh_pk y /\
      event_triggered tr bob (Respond1 alice bob gx gy y)
    )
    | InitiatorSendMsg3 bob gx gy k -> (
      let alice = prin in
      is_publishable tr gx /\ is_publishable tr gy /\
      is_knowable_by (principal_state_label alice sess_id) tr k /\
      event_triggered tr alice (Initiate2 alice bob gx gy k) /\
      (is_corrupt tr (principal_state_label alice sess_id) \/
      (exists y. k == dh y gx /\ is_dh_shared_key tr alice bob k /\ 
        event_triggered tr bob (Respond1 alice bob gx gy y)))
    )
    | ResponderReceivedMsg3 alice gx gy k -> (
      let bob = prin in
      is_publishable tr gx /\ is_publishable tr gy /\
      is_knowable_by (principal_state_label bob sess_id) tr k /\
      event_triggered tr bob (Respond2 alice bob gx gy k) /\
      (is_corrupt tr (principal_state_label bob sess_id) \/
      is_dh_shared_key tr alice bob k /\ event_triggered tr alice (Initiate2 alice bob gx gy k))
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}

/// The (local) event predicate.

let dh_event_pred: event_predicate dh_event =
  fun tr prin e ->
    match e with
    | Initiate1 alice bob x -> True
    | Respond1 alice bob gx gy y -> (
      is_publishable tr gx /\ is_publishable tr gy /\
      (exists sess_id. is_secret (principal_state_label bob sess_id) tr y) /\
      get_usage y == DhKey "DH.dh_key" /\
      gy = dh_pk y
    )
    | Initiate2 alice bob gx gy k -> (
      is_publishable tr gx /\ is_publishable tr gy /\
      (exists x sess_id. is_secret (principal_state_label alice sess_id) tr x /\
      gx = dh_pk x) /\
      (is_corrupt tr (principal_label bob) \/
      (exists y. k == dh y gx /\ is_dh_shared_key tr alice bob k /\ event_triggered tr bob (Respond1 alice bob gx gy y)))
    )
    | Respond2 alice bob gx gy k -> (
      is_corrupt tr (principal_label alice) \/ 
      (is_dh_shared_key tr alice bob k /\
      event_triggered tr alice (Initiate2 alice bob gx gy k))
    )

(* Couldn't we hide all of the following code in a function returning a record? *)

/// List of all local state predicates.

let all_sessions = [
  (pki_tag, typed_session_pred_to_session_pred (map_session_invariant pki_pred));
  (private_keys_tag, typed_session_pred_to_session_pred (map_session_invariant private_keys_pred));
  (dh_session_tag, typed_session_pred_to_session_pred dh_session_pred);
]

/// List of all local event predicates.

let all_events = [
  (dh_event_instance.tag, compile_event_pred dh_event_pred)
]

/// Create the global trace invariants.

let dh_trace_invs: trace_invariants (dh_crypto_invs) = {
  state_pred = mk_state_predicate dh_crypto_invs all_sessions;
  event_pred = mk_event_pred all_events;
}

instance dh_protocol_invs: protocol_invariants = {
  crypto_invs = dh_crypto_invs;
  trace_invs = dh_trace_invs;
}

/// Lemmas that the global state predicate contains all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_session_pred dh_protocol_invs) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  mk_global_session_pred_correct dh_protocol_invs all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_session_pred dh_protocol_invs) all_sessions)

val full_dh_session_pred_has_pki_invariant: squash (has_pki_invariant dh_protocol_invs)
let full_dh_session_pred_has_pki_invariant = all_sessions_has_all_sessions ()

val full_dh_session_pred_has_private_keys_invariant: squash (has_private_keys_invariant dh_protocol_invs)
let full_dh_session_pred_has_private_keys_invariant = all_sessions_has_all_sessions ()

val full_dh_session_pred_has_dh_invariant: squash (has_typed_session_pred dh_protocol_invs (dh_session_tag, dh_session_pred))
let full_dh_session_pred_has_dh_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred dh_protocol_invs) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct dh_protocol_invs all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred dh_protocol_invs) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred dh_protocol_invs) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred dh_protocol_invs) all_events))

val full_dh_event_pred_has_dh_invariant: squash (has_event_pred dh_protocol_invs dh_event_pred)
let full_dh_event_pred_has_dh_invariant = all_events_has_all_events ()
