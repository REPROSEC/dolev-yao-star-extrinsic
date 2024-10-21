module DY.Lib.State.PKI

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers
open DY.Lib.State.Tagged
open DY.Lib.State.Typed
open DY.Lib.State.Map
open DY.Lib.State.PrivateKeys // is_public_key_for

#set-options "--fuel 1 --ifuel 1"

/// This module defines a local Public-Key Infrastructure (PKI).
/// Public keys we use in a protocol may be authenticated in various ways,
/// for example by relying on certificate authorities (like TLS),
/// or by relying on off-band authentication (like Signal).
/// This authentication is abstracted away with this local PKI:
/// when a key is authenticated in some way (we don't know how),
/// we can add it to the local PKI store (using `install_public_key`).
/// Afterward, when we retrieve the public key of some principal (using `get_public_key`),
/// we will remember that it was authenticated beforehard
/// (i.e. it satisfy the predicate `is_public_key_for`).

(*** PKI types & invariants ***)

[@@ with_bytes bytes]
type pki_key = {
  ty:long_term_key_type;
  who:principal;
}

%splice [ps_pki_key] (gen_parser (`pki_key))
%splice [ps_pki_key_is_well_formed] (gen_is_well_formed_lemma (`pki_key))

[@@ with_bytes bytes]
type pki_value = {
  public_key: bytes;
}

%splice [ps_pki_value] (gen_parser (`pki_value))
%splice [ps_pki_value_is_well_formed] (gen_is_well_formed_lemma (`pki_value))

instance map_types_pki: map_types pki_key pki_value = {
  tag = "DY.Lib.State.PKI";
  ps_key_t = ps_pki_key;
  ps_value_t = ps_pki_value;
}

val pki_pred: {|crypto_invariants|} -> map_predicate pki_key pki_value
let pki_pred #cinvs = {
  pred = (fun tr prin sess_id (key: pki_key) value ->
    is_public_key_for tr value.public_key key.ty key.who
  );
  pred_later = (fun tr1 tr2 prin sess_id key value -> ());
  pred_knowable = (fun tr prin sess_id key value -> ());
}

val has_pki_invariant: {|protocol_invariants|} -> prop
let has_pki_invariant #invs =
  has_map_session_invariant pki_pred

val pki_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let pki_tag_and_invariant #ci = (|map_types_pki.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant pki_pred)|)

(*** PKI API ***)

[@@ "opaque_to_smt"]
val initialize_pki: prin:principal -> traceful state_id
let initialize_pki = initialize_map pki_key pki_value

[@@ "opaque_to_smt"]
val install_public_key: principal -> state_id -> long_term_key_type -> principal -> bytes -> traceful (option unit)
let install_public_key prin sess_id pk_type who pk =
  add_key_value prin sess_id ({ty = pk_type; who;}) ({public_key = pk;})

[@@ "opaque_to_smt"]
val get_public_key: principal -> state_id -> long_term_key_type -> principal -> traceful (option bytes)
let get_public_key prin sess_id pk_type who =
  let*? res = find_value prin sess_id ({ty = pk_type; who;}) in
  return (Some res.public_key)

val initialize_pki_invariant:
  {|protocol_invariants|} ->
  prin:principal -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant
  )
  (ensures (
    let (_, tr_out) = initialize_pki prin tr in
    trace_invariant tr_out
  ))
  [SMTPat (initialize_pki prin tr);
   SMTPat (has_pki_invariant);
   SMTPat (trace_invariant tr)]
let initialize_pki_invariant #invs prin tr =
  reveal_opaque (`%initialize_pki) (initialize_pki)

val install_public_key_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> pk_type:long_term_key_type -> who:principal -> pk:bytes -> tr:trace ->
  Lemma
  (requires
    is_public_key_for tr pk pk_type who /\
    trace_invariant tr /\
    has_pki_invariant
  )
  (ensures (
    let (_, tr_out) = install_public_key prin sess_id pk_type who pk tr in
    trace_invariant tr_out
  ))
  [SMTPat (install_public_key prin sess_id pk_type who pk tr);
   SMTPat (has_pki_invariant);
   SMTPat (trace_invariant tr)]
let install_public_key_invariant #invs prin sess_id pk_type who pk tr =
  reveal_opaque (`%install_public_key) (install_public_key)


val get_public_key_same_trace:
  prin:principal -> sess_id:state_id -> pk_type:long_term_key_type -> who:principal -> tr:trace ->
  Lemma
  (ensures (
    let (opt_public_key, tr_out) = get_public_key prin sess_id pk_type who tr in
    tr_out == tr
    ))
  [SMTPat (get_public_key prin sess_id pk_type who tr);]
let get_public_key_same_trace prin sess_id pk_type who tr =
  reveal_opaque (`%get_public_key) (get_public_key)

val get_public_key_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> pk_type:long_term_key_type -> who:principal -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant
  )
  (ensures (
    let (opt_public_key, tr_out) = get_public_key prin sess_id pk_type who tr in
      match opt_public_key with
      | None -> True
      | Some public_key ->
        is_public_key_for tr public_key pk_type who
  ))
  [SMTPat (get_public_key prin sess_id pk_type who tr);
   SMTPat (has_pki_invariant);
   SMTPat (trace_invariant tr)]
let get_public_key_invariant #invs prin sess_id pk_type who tr =
  reveal_opaque (`%get_public_key) (get_public_key)
