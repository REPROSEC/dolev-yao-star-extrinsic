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
type private_key_type =
  | PkDec: [@@@with_parser #bytes ps_string] usage:string -> private_key_type
  | Sign: [@@@with_parser #bytes ps_string] usage:string -> private_key_type

%splice [ps_private_key_type] (gen_parser (`private_key_type))
%splice [ps_private_key_type_is_well_formed] (gen_is_well_formed_lemma (`private_key_type))

[@@ with_bytes bytes]
type private_key_key = {
  ty:private_key_type;
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

val is_private_key_for:
  {|crypto_invariants|} -> trace ->
  bytes -> private_key_type -> principal -> prop
let is_private_key_for #cinvs tr sk sk_type who =
  match sk_type with
  | PkDec usg -> (
    is_decryption_key usg (principal_label who) tr sk
  )
  | Sign usg -> (
    is_signature_key usg (principal_label who) tr sk
  )

// The `#_` at the end is a workaround for FStarLang/FStar#3286
val private_keys_pred: {|crypto_invariants|} -> map_predicate private_key_key private_key_value #_
let private_keys_pred #cinvs = {
  pred = (fun tr prin sess_id key value ->
    is_private_key_for tr value.private_key key.ty prin
  );
  pred_later = (fun tr1 tr2 prin sess_id key value -> ());
  pred_knowable = (fun tr prin sess_id key value -> ());
}

val has_private_keys_invariant: protocol_invariants -> prop
let has_private_keys_invariant invs =
  has_map_session_invariant invs private_keys_pred

val private_keys_tag_and_invariant: {|crypto_invariants|} -> string & local_bytes_state_predicate
let private_keys_tag_and_invariant #ci = (map_types_private_keys.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant private_keys_pred))

val private_key_type_to_usage:
  private_key_type ->
  usage
let private_key_type_to_usage sk_type =
  match sk_type with
  | PkDec usg -> PkdecKey usg
  | Sign usg -> SigKey usg

(*** Private Keys API ***)

[@@ "opaque_to_smt"]
val initialize_private_keys: prin:principal -> crypto nat
let initialize_private_keys = initialize_map private_key_key private_key_value #_ // another workaround for FStarLang/FStar#3286

[@@ "opaque_to_smt"]
val generate_private_key: principal -> nat -> private_key_type -> crypto (option unit)
let generate_private_key prin sess_id sk_type =
  let* sk = mk_rand (private_key_type_to_usage sk_type) (principal_label prin) 64 in //TODO
  add_key_value prin sess_id ({ty = sk_type}) ({private_key = sk;})

[@@ "opaque_to_smt"]
val get_private_key: principal -> nat -> private_key_type -> crypto (option bytes)
let get_private_key prin sess_id sk_type =
  let*? res = find_value prin sess_id ({ty = sk_type}) in
  return (Some res.private_key)

val initialize_private_keys_invariant:
  {|invs:protocol_invariants|} ->
  prin:principal -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant invs
  )
  (ensures (
    let (_, tr_out) = initialize_private_keys prin tr in
    trace_invariant tr_out
  ))
  [SMTPat (initialize_private_keys prin tr);
   SMTPat (has_private_keys_invariant invs);
   SMTPat (trace_invariant tr)]
let initialize_private_keys_invariant #invs prin tr =
  reveal_opaque (`%initialize_private_keys) (initialize_private_keys)

val generate_private_key_invariant:
  {|invs:protocol_invariants|} ->
  prin:principal -> sess_id:nat -> sk_type:private_key_type -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant invs
  )
  (ensures (
    let (_, tr_out) = generate_private_key prin sess_id sk_type tr in
    trace_invariant tr_out
  ))
  [SMTPat (generate_private_key prin sess_id sk_type tr);
   SMTPat (has_private_keys_invariant invs);
   SMTPat (trace_invariant tr)]
let generate_private_key_invariant #invs prin sess_id sk_type tr =
  reveal_opaque (`%generate_private_key) (generate_private_key)

val get_private_key_invariant:
  {|invs:protocol_invariants|} ->
  prin:principal -> sess_id:nat -> pk_type:private_key_type -> tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant invs
  )
  (ensures (
    let (opt_private_key, tr_out) = get_private_key prin sess_id pk_type tr in
    tr_out == tr /\ (
      match opt_private_key with
      | None -> True
      | Some private_key ->
        is_private_key_for tr private_key pk_type prin
    )
  ))
  [SMTPat (get_private_key prin sess_id pk_type tr);
   SMTPat (has_private_keys_invariant invs);
   SMTPat (trace_invariant tr)]
let get_private_key_invariant #invs prin sess_id pk_type tr =
  reveal_opaque (`%get_private_key) (get_private_key)
