module DY.Lib.Comparse.Glue

open Comparse
open DY.Core

instance bytes_like_bytes: bytes_like bytes = {
  length = length;

  empty = literal_to_bytes FStar.Seq.empty;
  empty_length = (fun () -> length_literal_to_bytes FStar.Seq.empty);
  recognize_empty = (fun b ->
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

val bytes_invariant_is_pre_compatible:
  cpreds:crypto_predicates -> tr:trace ->
  Lemma
  (bytes_pre_is_compatible (bytes_invariant cpreds tr))
  [SMTPat (bytes_pre_is_compatible (bytes_invariant cpreds tr))]
let bytes_invariant_is_pre_compatible cpreds tr =
  bytes_pre_is_compatible_intro #bytes (bytes_invariant cpreds tr)
    ()
    (fun b1 b2 -> ())
    (fun b i -> ())
    (fun sz n -> ())

val is_publishable_is_pre_compatible:
  cpreds:crypto_predicates -> tr:trace ->
  Lemma
  (bytes_pre_is_compatible (is_publishable cpreds tr))
  [SMTPat (bytes_pre_is_compatible (is_publishable cpreds tr))]
let is_publishable_is_pre_compatible cpreds tr =
  bytes_pre_is_compatible_intro #bytes (is_publishable cpreds tr)
    (literal_to_bytes_is_publishable cpreds tr FStar.Seq.empty)
    (fun b1 b2 -> concat_preserves_publishability cpreds tr b1 b2)
    (fun b i -> split_preserves_publishability cpreds tr b i)
    (fun sz n -> literal_to_bytes_is_publishable cpreds tr (FStar.Endianness.n_to_be sz n))

val is_knowable_by_is_pre_compatible:
  cpreds:crypto_predicates -> lab:label -> tr:trace ->
  Lemma
  (bytes_pre_is_compatible (is_knowable_by cpreds lab tr))
  [SMTPat (bytes_pre_is_compatible (is_knowable_by cpreds lab tr))]
let is_knowable_by_is_pre_compatible cpreds lab tr =
  bytes_pre_is_compatible_intro #bytes (is_knowable_by cpreds lab tr)
    ()
    (fun b1 b2 -> concat_preserves_knowability cpreds lab tr b1 b2)
    (fun b i -> split_preserves_knowability cpreds lab tr b i)
    (fun sz n -> ())

val parse_serialize_inv_lemma_smtpat:
  #bytes:Type0 -> {|bl:bytes_like bytes|} ->
  a:Type -> {|ps_a:parseable_serializeable bytes a|} ->
  x:a ->
  Lemma
  (ensures parse a (serialize #bytes a x) == Some x)
  [SMTPat (parse #bytes #bl a #ps_a (serialize #bytes a #ps_a x))]
let parse_serialize_inv_lemma_smtpat #bytes #bl a #ps_a x =
  parse_serialize_inv_lemma #bytes a #ps_a x
