module DY.Lib.Comparse.Glue

open Comparse
open DY.Core

/// This module instantiate Comparse with DY*'s bytes.

/// The `bytes_like` instantiation on DY*'s bytes.

instance bytes_like_bytes: bytes_like bytes = {
  length = length;

  empty = literal_to_bytes FStar.Seq.empty;
  empty_length = (fun () -> length_literal_to_bytes FStar.Seq.empty);
  recognize_empty = (fun b ->
  literal_to_bytes_to_literal FStar.Seq.empty;
    match bytes_to_literal b with
    | None -> false
    | Some lit ->
      if Seq.length lit = 0 then (
        assert(lit `FStar.Seq.eq` FStar.Seq.empty);
        bytes_to_literal_to_bytes b;
        true
      ) else (
        length_literal_to_bytes FStar.Seq.empty;
        false
      )
  );

  concat = concat;
  concat_length = (fun b1 b2 -> concat_length b1 b2);

  split = split;
  split_length = (fun b i -> split_length b i);

  split_concat = (fun b1 b2 -> split_concat b1 b2);

  concat_split = (fun b i -> concat_split b i);

  to_nat = (fun b ->
    bytes_to_literal_to_bytes b;
    match bytes_to_literal b with
    | None -> None
    | Some lit ->  (
      FStar.Endianness.lemma_be_to_n_is_bounded lit;
      Some (FStar.Endianness.be_to_n lit)
    )
  );
  from_nat = (fun sz n ->
    literal_to_bytes (FStar.Endianness.n_to_be sz n)
  );

  from_to_nat = (fun sz n ->
    literal_to_bytes_to_literal (FStar.Endianness.n_to_be sz n)
  );

  to_from_nat = (fun b ->
    bytes_to_literal_to_bytes b
  );
}

/// Compability of some DY*'s predicates with concat and split.

val bytes_well_formed_is_pre_compatible:
  tr:trace ->
  Lemma
  (bytes_pre_is_compatible (bytes_well_formed tr))
  [SMTPat (bytes_pre_is_compatible (bytes_well_formed tr))]
let bytes_well_formed_is_pre_compatible tr =
  enable_bytes_well_formed_smtpats tr;
  bytes_pre_is_compatible_intro #bytes (bytes_well_formed tr)
    ()
    (fun b1 b2 -> ())
    (fun b i -> ())
    (fun sz n -> ())

val bytes_invariant_is_pre_compatible:
  {|crypto_invariants|} -> tr:trace ->
  Lemma
  (bytes_pre_is_compatible (bytes_invariant tr))
  [SMTPat (bytes_pre_is_compatible (bytes_invariant tr))]
let bytes_invariant_is_pre_compatible #cinvs tr =
  bytes_pre_is_compatible_intro #bytes (bytes_invariant tr)
    ()
    (fun b1 b2 -> ())
    (fun b i -> ())
    (fun sz n -> ())

val is_publishable_is_pre_compatible:
  {|crypto_invariants|} -> tr:trace ->
  Lemma
  (bytes_pre_is_compatible (is_publishable tr))
  [SMTPat (bytes_pre_is_compatible (is_publishable tr))]
let is_publishable_is_pre_compatible #cinvs tr =
  bytes_pre_is_compatible_intro #bytes (is_publishable tr)
    (literal_to_bytes_is_publishable tr FStar.Seq.empty)
    (fun b1 b2 -> concat_preserves_publishability tr b1 b2)
    (fun b i -> split_preserves_publishability tr b i)
    (fun sz n -> literal_to_bytes_is_publishable tr (FStar.Endianness.n_to_be sz n))

val is_knowable_by_is_pre_compatible:
  {|crypto_invariants|} -> lab:label -> tr:trace ->
  Lemma
  (bytes_pre_is_compatible (is_knowable_by lab tr))
  [SMTPat (bytes_pre_is_compatible (is_knowable_by lab tr))]
let is_knowable_by_is_pre_compatible #cinvs lab tr =
  bytes_pre_is_compatible_intro #bytes (is_knowable_by lab tr)
    (literal_to_bytes_is_publishable tr Seq.empty)
    (fun b1 b2 -> concat_preserves_knowability lab tr b1 b2)
    (fun b i -> split_preserves_knowability lab tr b i)
    (fun sz n -> (literal_to_bytes_is_publishable tr (FStar.Endianness.n_to_be sz n)))

/// Add an SMT pattern that serialization is injective.

val parse_serialize_inv_lemma_smtpat:
  #bytes:Type0 -> {|bl:bytes_like bytes|} ->
  a:Type -> {|ps_a:parseable_serializeable bytes a|} ->
  x:a ->
  Lemma
  (ensures parse a (serialize #bytes a x) == Some x)
  [SMTPat ((serialize #bytes a #ps_a x))]
let parse_serialize_inv_lemma_smtpat #bytes #bl a #ps_a x =
  parse_serialize_inv_lemma #bytes a #ps_a x

/// Extra SMT patterns, with a switch to enable them

[@@"opaque_to_smt"]
let comparse_wf_lemmas_smtpats_enabled (dummy:unit) = True

val enable_comparse_wf_lemmas_smtpats:
  dummy:unit ->
  squash (comparse_wf_lemmas_smtpats_enabled dummy)
let enable_comparse_wf_lemmas_smtpats dummy =
  normalize_term_spec (comparse_wf_lemmas_smtpats_enabled dummy)

val serialize_wf_lemma_smtpat:
  a:Type -> {|parseable_serializeable bytes a|} -> pre:bytes_compatible_pre bytes -> x:a -> dummy:unit ->
  Lemma
  (requires is_well_formed a pre x)
  (ensures pre (serialize a x))
  [SMTPat (pre (serialize a x));
   SMTPat (comparse_wf_lemmas_smtpats_enabled dummy);
  ]
let serialize_wf_lemma_smtpat a #ps pre x dummy =
  serialize_wf_lemma a pre x

val parse_wf_lemma_smtpat:
  a:Type -> {|parseable_serializeable bytes a|} -> pre:bytes_compatible_pre bytes -> buf:bytes -> dummy:unit ->
  Lemma
  (requires pre buf)
  (ensures (
    match parse a buf with
    | Some x -> is_well_formed a pre x
    | None -> True
  ))
  [SMTPat (pre buf);
   SMTPat (parse a buf);
   SMTPat (comparse_wf_lemmas_smtpats_enabled dummy);
  ]
let parse_wf_lemma_smtpat a #ps pre x dummy =
  parse_wf_lemma a pre x
