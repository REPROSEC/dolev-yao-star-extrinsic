module DY.Lib.State.PKI

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Map

#set-options "--fuel 1 --ifuel 1"

(*** PKI types & invariants ***)

type public_key_type =
  | PkEnc: public_key_type
  | Verify: public_key_type

%splice [ps_public_key_type] (gen_parser (`public_key_type))
%splice [ps_public_key_type_is_well_formed] (gen_is_well_formed_lemma (`public_key_type))

type pki_key (bytes:Type0) {|bytes_like bytes|} = {
  ty:public_key_type;
  who:principal;
}

%splice [ps_pki_key] (gen_parser (`pki_key))
%splice [ps_pki_key_is_well_formed] (gen_is_well_formed_lemma (`pki_key))

type pki_value (bytes:Type0) {|bytes_like bytes|} = {
  public_key: bytes;
}

%splice [ps_pki_value] (gen_parser (`pki_value))
%splice [ps_pki_value_is_well_formed] (gen_is_well_formed_lemma (`pki_value))

val pki_types: map_types bytes
let pki_types = {
  key = pki_key bytes;
  ps_key = ps_pki_key;
  value = pki_value bytes;
  ps_value = ps_pki_value;
}

val is_public_key_for:
  crypto_predicates -> trace ->
  bytes -> public_key_type -> principal -> prop
let is_public_key_for cpreds tr pk pk_type who =
    match pk_type with
    | PkEnc -> (
      is_encryption_key cpreds (principal_label who) tr pk
    )
    | Verify -> (
      is_verification_key cpreds (principal_label who) tr pk
    )

val pki_pred: map_predicate pki_types
let pki_pred = {
  pred = (fun cpreds tr prin sess_id (key:pki_types.key) value ->
    is_public_key_for cpreds tr value.public_key key.ty key.who
  );
  pred_later = (fun cpreds tr1 tr2 prin sess_id key value -> ());
  pred_knowable = (fun cpreds tr prin sess_id key value -> ());
}

val pki_label: string
let pki_label = "DY.Lib.State.PKI"

val has_pki_invariant: protocol_predicates -> prop
let has_pki_invariant pr =
  has_map_session_invariant pki_pred pki_label pr

(*** PKI API ***)

val initialize_pki: prin:principal -> crypto nat
let initialize_pki = initialize_map pki_types pki_label

val install_public_key: principal -> nat -> public_key_type -> principal -> bytes -> crypto (option unit)
let install_public_key prin sess_id pk_type who pk =
  add_key_value pki_types pki_label prin sess_id ({ty = pk_type; who;}) ({public_key = pk;})

val get_public_key: principal -> nat -> public_key_type -> principal -> crypto (option bytes)
let get_public_key prin sess_id pk_type who =
  let*? res = find_value pki_types pki_label prin sess_id ({ty = pk_type; who;}) in
  return (Some res.public_key)

val initialize_pki_invariant:
  preds:protocol_predicates ->
  prin:principal -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_pki_invariant preds
  )
  (ensures (
    let (_, tr_out) = initialize_pki prin tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (initialize_pki prin tr);
   SMTPat (has_pki_invariant preds);
   SMTPat (trace_invariant preds tr)]
let initialize_pki_invariant preds prin tr = ()

val install_public_key_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> pk_type:public_key_type -> who:principal -> pk:bytes -> tr:trace ->
  Lemma
  (requires
    is_public_key_for preds.crypto_preds tr pk pk_type who /\
    trace_invariant preds tr /\
    has_pki_invariant preds
  )
  (ensures (
    let (_, tr_out) = install_public_key prin sess_id pk_type who pk tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (install_public_key prin sess_id pk_type who pk tr);
   SMTPat (has_pki_invariant preds);
   SMTPat (trace_invariant preds tr)]
let install_public_key_invariant preds prin sess_id pk_type who pk tr = ()

val get_public_key_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> pk_type:public_key_type -> who:principal -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_pki_invariant preds
  )
  (ensures (
    let (opt_public_key, tr_out) = get_public_key prin sess_id pk_type who tr in
    tr_out == tr /\ (
      match opt_public_key with
      | None -> True
      | Some public_key ->
        is_public_key_for preds.crypto_preds tr public_key pk_type who
    )
  ))
  [SMTPat (get_public_key prin sess_id pk_type who tr);
   SMTPat (has_pki_invariant preds);
   SMTPat (trace_invariant preds tr)]
let get_public_key_invariant preds prin sess_id pk_type who tr = ()
