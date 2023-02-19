module DY.Lib.State.PrivateKeys

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.State.Map

#set-options "--fuel 1 --ifuel 1"

(*** Private keys types & invariants ***)

type private_key_type =
  | PkEnc: private_key_type
  | Sign: private_key_type

%splice [ps_private_key_type] (gen_parser (`private_key_type))
%splice [ps_private_key_type_is_well_formed] (gen_is_well_formed_lemma (`private_key_type))

type private_key_value (bytes:Type0) {|bytes_like bytes|} = {
  private_key: bytes;
}

%splice [ps_private_key_value] (gen_parser (`private_key_value))
%splice [ps_private_key_value_is_well_formed] (gen_is_well_formed_lemma (`private_key_value))

val private_keys_types: map_types bytes
let private_keys_types = {
  key = private_key_type;
  ps_key = ps_private_key_type;
  value = private_key_value bytes;
  ps_value = ps_private_key_value;
}

val is_private_key_for:
  crypto_predicates -> trace ->
  bytes -> private_key_type -> principal -> prop
let is_private_key_for cpreds tr sk sk_type who =
    match sk_type with
    | PkEnc -> (
      bytes_invariant cpreds tr sk /\
      get_label sk == principal_label who
    )
    | Sign -> (
      bytes_invariant cpreds tr sk /\
      get_label sk == principal_label who
    )

val private_keys_pred: map_predicate private_keys_types
let private_keys_pred = {
  pred = (fun cpreds tr prin sess_id (key:private_keys_types.key) value ->
    is_private_key_for cpreds tr value.private_key key prin
  );
  pred_later = (fun cpreds tr1 tr2 prin sess_id key value -> ());
  pred_knowable = (fun cpreds tr prin sess_id key value -> ());
}

val private_keys_label: string
let private_keys_label = "DY.Lib.State.PrivateKeys"

val has_private_keys_invariant: protocol_predicates -> prop
let has_private_keys_invariant pr =
  has_map_session_invariant private_keys_pred private_keys_label pr

(*** Private Keys API ***)

val initialize_private_keys: prin:principal -> crypto nat
let initialize_private_keys = initialize_map private_keys_types private_keys_label

val generate_private_key: principal -> nat -> private_key_type -> crypto (option unit)
let generate_private_key prin sess_id sk_type =
  let* sk = mk_rand (principal_label prin) 64 in //TODO
  add_key_value private_keys_types private_keys_label prin sess_id sk_type ({private_key = sk;})

val get_private_key: principal -> nat -> private_key_type -> crypto (option bytes)
let get_private_key prin sess_id sk_type =
  let*? res = find_value private_keys_types private_keys_label prin sess_id sk_type in
  return (Some res.private_key)

val initialize_private_keys_invariant:
  preds:protocol_predicates ->
  prin:principal -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_private_keys_invariant preds
  )
  (ensures (
    let (_, tr_out) = initialize_private_keys prin tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (initialize_private_keys prin tr);
   SMTPat (has_private_keys_invariant preds);
   SMTPat (trace_invariant preds tr)]
let initialize_private_keys_invariant preds prin tr = ()

val generate_private_key_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> sk_type:private_key_type -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_private_keys_invariant preds
  )
  (ensures (
    let (_, tr_out) = generate_private_key prin sess_id sk_type tr in
    trace_invariant preds tr_out
  ))
  [SMTPat (generate_private_key prin sess_id sk_type tr);
   SMTPat (has_private_keys_invariant preds);
   SMTPat (trace_invariant preds tr)]
let generate_private_key_invariant preds prin sess_id sk_type tr = ()

val get_private_key_invariant:
  preds:protocol_predicates ->
  prin:principal -> sess_id:nat -> pk_type:private_key_type -> tr:trace ->
  Lemma
  (requires
    trace_invariant preds tr /\
    has_private_keys_invariant preds
  )
  (ensures (
    let (opt_private_key, tr_out) = get_private_key prin sess_id pk_type tr in
    tr_out == tr /\ (
      match opt_private_key with
      | None -> True
      | Some private_key ->
        is_private_key_for preds.crypto_preds tr private_key pk_type prin
    )
  ))
  [SMTPat (get_private_key prin sess_id pk_type tr);
   SMTPat (has_private_keys_invariant preds);
   SMTPat (trace_invariant preds tr)]
let get_private_key_invariant preds prin sess_id pk_type tr = ()
