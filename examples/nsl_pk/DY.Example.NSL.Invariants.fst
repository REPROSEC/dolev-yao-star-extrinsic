module DY.Example.NSL.Invariants

open Comparse
open DY.Core
open DY.Lib
open DY.Example.NSL.Protocol.Total.Proof
open DY.Example.NSL.Protocol.Stateful
open DY.Example.NSL.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0"

/// Crypto Usages

instance nsl_crypto_usages: crypto_usages = default_crypto_usages

/// List of all local pkenc predicates

let all_pkenc_tag_and_preds = [
  nsl_tag_and_pkenc_pred;
]

let nsl_crypto_predicates: crypto_predicates nsl_crypto_usages = {
  default_crypto_predicates nsl_crypto_usages with
  pkenc_pred = mk_pkenc_predicate all_pkenc_tag_and_preds
}

/// Crypto Invariants

instance nsl_crypto_invariants: crypto_invariants = {
  usages = nsl_crypto_usages;
  preds = nsl_crypto_predicates;
}

// fuel 1 is a workaround for FStarLang/FStar#3360
#push-options "--fuel 1"
val nsl_crypto_invariants_has_nsl_crypto_invariants:
  unit ->
  Lemma (has_nsl_crypto_invariants #nsl_crypto_invariants)
let nsl_crypto_invariants_has_nsl_crypto_invariants () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst all_pkenc_tag_and_preds));
  mk_pkenc_predicate_correct nsl_crypto_invariants all_pkenc_tag_and_preds;
  norm_spec [delta_only [`%all_pkenc_tag_and_preds; `%for_allP]; iota; zeta] (for_allP (has_pkenc_predicate nsl_crypto_invariants) all_pkenc_tag_and_preds)
#pop-options

/// List of all local state predicates.

let all_state_tag_and_preds = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (local_state_nsl_session.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_nsl);
]

/// List of all local event predicates.

let all_event_tag_and_preds = [
  (event_nsl_event.tag, compile_event_pred event_predicate_nsl)
]

/// Trace Invariant

let nsl_trace_invariants: trace_invariants nsl_crypto_invariants = {
  state_pred = mk_state_pred nsl_crypto_invariants all_state_tag_and_preds;
  event_pred = mk_event_pred all_event_tag_and_preds;
}

/// Protocol Invariants

instance nsl_protocol_invariants: protocol_invariants = {
  crypto_invs = nsl_crypto_invariants;
  trace_invs = nsl_trace_invariants;
}

// fuel 1 is a workaround for FStarLang/FStar#3360
#push-options "--fuel 1"
val nsl_protocol_invariants_has_nsl_invariants:
  unit ->
  Lemma (has_nsl_invariants #nsl_protocol_invariants)
let nsl_protocol_invariants_has_nsl_invariants () =
  nsl_crypto_invariants_has_nsl_crypto_invariants ();

  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_state_tag_and_preds)));
  mk_state_pred_correct nsl_protocol_invariants all_state_tag_and_preds;
  norm_spec [delta_only [`%all_state_tag_and_preds; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate nsl_protocol_invariants) all_state_tag_and_preds);

  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_event_tag_and_preds)));
  mk_event_pred_correct nsl_protocol_invariants all_event_tag_and_preds;
  norm_spec [delta_only [`%all_event_tag_and_preds; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred nsl_protocol_invariants) all_event_tag_and_preds)
#pop-options
