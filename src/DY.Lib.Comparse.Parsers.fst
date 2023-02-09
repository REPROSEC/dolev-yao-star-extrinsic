module DY.Lib.Comparse.Parsers

open DY.Core.Label.Type
open Comparse

(*** Parser for principals ***)

val ps_char: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes Char.char
let ps_char #bytes #bl =
  let char_pred (n:nat_lbytes 4) = n < 0xd7ff || (n >= 0xe000 && n <= 0x10ffff) in
  mk_isomorphism Char.char (refine (ps_nat_lbytes 4) char_pred) (fun c -> Char.char_of_int c) (fun c -> Char.int_of_char c)

val ps_char_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes -> c:Char.char ->
  Lemma (is_well_formed_prefix ps_char pre c)
  [SMTPat (is_well_formed_prefix ps_char pre c)]
let ps_char_is_well_formed #bytes #bl pre c = ()

val ps_string: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes string
let ps_string #bytes #bl =
  isomorphism (ps_seq ps_char) ({
    a_to_b = (fun s -> String.string_of_list (Seq.seq_to_list s));
    b_to_a = (fun s -> Seq.seq_of_list (String.list_of_string s));
    a_to_b_to_a = (fun s -> String.list_of_string_of_list (Seq.seq_to_list s); Seq.lemma_seq_list_bij s);
    b_to_a_to_b = (fun s -> String.string_of_list_of_string s; Seq.lemma_list_seq_bij (String.list_of_string s));
  })

val ps_string_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes -> s:string ->
  Lemma (is_well_formed_prefix ps_string pre s)
  [SMTPat (is_well_formed_prefix ps_string pre s)]
let ps_string_is_well_formed #bytes #bl pre s =
  Seq.lemma_list_seq_bij (String.list_of_string s);
  for_allP_eq (is_well_formed_prefix ps_char pre) (String.list_of_string s)

[@@is_parser; is_parser_for (`%principal)]
val ps_principal: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes principal
let ps_principal #bytes #bl =
  mk_trivial_isomorphism ps_string

(*** Parser for nats ***)

[@@is_parser; is_parser_for (`%nat)]
val ps_nat: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes nat
let ps_nat #bytes #bl = ps_nat
