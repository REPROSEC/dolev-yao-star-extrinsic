module DY.Lib.State.PrivateKeys

open Comparse
open DY.Core
open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers
open DY.Lib.State.Tagged
open DY.Lib.State.Typed
open DY.Lib.State.Map

#set-options "--fuel 1 --ifuel 1"

/// This module defines a state to store private keys for a principal.
/// Private keys can be generated with `generate_private_key`
/// and obtained back with `get_private_key`.

(*** Private keys types & invariants ***)

[@@ with_bytes bytes]
type long_term_key_type =
  | LongTermPkeKey: [@@@ with_parser #bytes ps_string] usage:string -> long_term_key_type
  | LongTermSigKey: [@@@ with_parser #bytes ps_string] usage:string -> long_term_key_type

%splice [ps_long_term_key_type] (gen_parser (`long_term_key_type))
%splice [ps_long_term_key_type_is_well_formed] (gen_is_well_formed_lemma (`long_term_key_type))

[@@ with_bytes bytes]
type private_key_key = {
  ty:long_term_key_type;
}

%splice [ps_private_key_key] (gen_parser (`private_key_key))
%splice [ps_private_key_key_is_well_formed] (gen_is_well_formed_lemma (`private_key_key))

[@@ with_bytes bytes]
type private_key_value = {
  private_key: bytes;
}

%splice [ps_private_key_value] (gen_parser (`private_key_value))
%splice [ps_private_key_value_is_well_formed] (gen_is_well_formed_lemma (`private_key_value))

instance map_types_private_keys: map_types private_key_key private_key_value = {
  tag = "DY.Lib.State.PrivateKeys";
  ps_key_t = ps_private_key_key;
  ps_value_t = ps_private_key_value;
}

val long_term_key_label: principal -> label
let long_term_key_label prin =
  principal_tag_label prin "DY.Lib.State.PrivateKeys"

type long_term_key_usage_data = {
  who: principal;
}

%splice [ps_long_term_key_usage_data] (gen_parser (`long_term_key_usage_data))

instance parseable_serializeable_bytes_long_term_key_usage_data: parseable_serializeable bytes long_term_key_usage_data =
  mk_parseable_serializeable ps_long_term_key_usage_data

val long_term_key_type_to_usage:
  long_term_key_type -> principal ->
  usage
let long_term_key_type_to_usage sk_type who =
  match sk_type with
  | LongTermPkeKey usg -> PkeKey usg (serialize _ {who})
  | LongTermSigKey usg -> SigKey usg (serialize _ {who})

val is_private_key_for:
  {|crypto_invariants|} -> trace ->
  bytes -> long_term_key_type -> principal -> prop
let is_private_key_for #cinvs tr sk sk_type who =
  match sk_type with
  | LongTermPkeKey usg -> (
    is_decryption_key (long_term_key_type_to_usage sk_type who) (long_term_key_label who) tr sk
  )
  | LongTermSigKey usg -> (
    is_signature_key (long_term_key_type_to_usage sk_type who) (long_term_key_label who) tr sk
  )

val is_public_key_for:
  {|crypto_invariants|} -> trace ->
  bytes -> long_term_key_type -> principal -> prop
let is_public_key_for #cinvs tr pk pk_type who =
  match pk_type with
  | LongTermPkeKey usg -> (
    is_encryption_key (long_term_key_type_to_usage pk_type who) (long_term_key_label who) tr pk
  )
  | LongTermSigKey usg -> (
    is_verification_key (long_term_key_type_to_usage pk_type who) (long_term_key_label who) tr pk
  )

#push-options "--z3rlimit 10"
val private_keys_pred: {|crypto_invariants|} -> map_predicate private_key_key private_key_value
let private_keys_pred #cinvs = {
  pred = (fun tr prin sess_id key value ->
    is_private_key_for tr value.private_key key.ty prin
  );
  pred_later = (fun tr1 tr2 prin sess_id key value -> ());
  pred_knowable = (fun tr prin sess_id key value -> ());
}
#pop-options

val private_keys_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let private_keys_tag_and_invariant #ci = mk_map_state_tag_and_pred private_keys_pred

unfold
val has_private_keys_invariant: {|protocol_invariants|} -> prop
let has_private_keys_invariant #invs =
  has_local_bytes_state_predicate private_keys_tag_and_invariant

(*** Private Keys API ***)

[@@ "opaque_to_smt"]
val initialize_private_keys: prin:principal -> traceful state_id
let initialize_private_keys = initialize_map private_key_key private_key_value

[@@ "opaque_to_smt"]
val generate_private_key: principal -> state_id -> long_term_key_type -> traceful (option unit)
let generate_private_key prin sess_id sk_type =
  let* sk = mk_rand (long_term_key_type_to_usage sk_type prin) (long_term_key_label prin) 64 in //TODO
  add_key_value prin sess_id ({ty = sk_type}) ({private_key = sk;})

[@@ "opaque_to_smt"]
val get_private_key: principal -> state_id -> long_term_key_type -> traceful (option bytes)
let get_private_key prin sess_id sk_type =
  let*? res = find_value prin sess_id ({ty = sk_type}) in
  return (Some res.private_key)

[@@ "opaque_to_smt"]
val compute_public_key: principal -> state_id -> long_term_key_type -> traceful (option bytes)
let compute_public_key prin sess_id sk_type =
  let*? res = find_value prin sess_id ({ty = sk_type}) in
  match sk_type with
  | LongTermPkeKey _ ->
    return (Some (pk res.private_key))
  | LongTermSigKey _ ->
    return (Some (vk res.private_key))

val initialize_private_keys_invariant:
  {|protocol_invariants|} ->
  prin:principal -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant
  )
  (ensures (
    let (_, tr_out) = initialize_private_keys prin tr in
    trace_invariant tr_out
  ))
  [SMTPat (initialize_private_keys prin tr);
   SMTPat (has_private_keys_invariant);
   SMTPat (trace_invariant tr)]
let initialize_private_keys_invariant #invs prin tr =
  reveal_opaque (`%initialize_private_keys) (initialize_private_keys)

val generate_private_key_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> sk_type:long_term_key_type -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant
  )
  (ensures (
    let (_, tr_out) = generate_private_key prin sess_id sk_type tr in
    trace_invariant tr_out
  ))
  [SMTPat (generate_private_key prin sess_id sk_type tr);
   SMTPat (has_private_keys_invariant);
   SMTPat (trace_invariant tr)]
let generate_private_key_invariant #invs prin sess_id sk_type tr =
  reveal_opaque (`%generate_private_key) (generate_private_key)

val get_private_key_same_trace:
  prin:principal -> sess_id:state_id -> pk_type:long_term_key_type -> tr:trace ->
  Lemma
  (ensures (
    let (opt_private_key, tr_out) = get_private_key prin sess_id pk_type tr in
    tr_out == tr
  ))
  [SMTPat (get_private_key prin sess_id pk_type tr);]
let get_private_key_same_trace prin sess_id pk_type tr =
  reveal_opaque (`%get_private_key) (get_private_key)


val get_private_key_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> pk_type:long_term_key_type -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant
  )
  (ensures (
    let (opt_private_key, tr_out) = get_private_key prin sess_id pk_type tr in
    match opt_private_key with
    | None -> True
    | Some private_key ->
        is_private_key_for tr private_key pk_type prin
  ))
  [SMTPat (get_private_key prin sess_id pk_type tr);
   SMTPat (has_private_keys_invariant);
   SMTPat (trace_invariant tr)]
let get_private_key_invariant #invs prin sess_id pk_type tr =
  reveal_opaque (`%get_private_key) (get_private_key)


val compute_public_key_same_trace:
  prin:principal -> sess_id:state_id -> pk_type:long_term_key_type -> tr:trace ->
  Lemma
  (ensures (
    let (opt_private_key, tr_out) = compute_public_key prin sess_id pk_type tr in
    tr_out == tr
  ))
  [SMTPat (compute_public_key prin sess_id pk_type tr);]
let compute_public_key_same_trace prin sess_id pk_type tr =
  reveal_opaque (`%compute_public_key) (compute_public_key)


val compute_public_key_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sess_id:state_id -> pk_type:long_term_key_type -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant
  )
  (ensures (
    let (opt_private_key, tr_out) = compute_public_key prin sess_id pk_type tr in
    match opt_private_key with
    | None -> True
    | Some private_key ->
        is_public_key_for tr private_key pk_type prin
  ))
  [SMTPat (compute_public_key prin sess_id pk_type tr);
   SMTPat (has_private_keys_invariant);
   SMTPat (trace_invariant tr)]
let compute_public_key_invariant #invs prin sess_id pk_type tr =
  reveal_opaque (`%compute_public_key) (compute_public_key)
