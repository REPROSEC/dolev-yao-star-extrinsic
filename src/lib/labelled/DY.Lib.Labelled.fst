module DY.Lib.Labelled

open Comparse
open DY.Lib.Comparse.Glue
open DY.Core

class labelled (a:Type) =
{
  extract_label : a -> GTot label
}

let less_secret (#a #b:Type) {| labelled a |} {| labelled b |} (tr:trace) (x:a) (y:b) =
  can_flow tr (extract_label x) (extract_label y)

let more_secret (#a #b:Type) {| labelled a |} {| labelled b |} (tr:trace) (x:a) (y:b) =
  can_flow tr (extract_label y) (extract_label x)

let equally_secret (#a #b:Type) {| labelled a |} {| labelled b |} (x:a) (y:b) =
  always_equivalent (extract_label x) (extract_label y)

let secrecy_reflexive (#a:Type) {| labelled a |} (x:a)
  : Lemma (equally_secret x x)
  = ()

let secrecy_transitive (#a #b #c:Type) {| labelled a |} {| labelled b |} {| labelled c |} (tr:trace) (x:a) (y:b) (z:c)
  : Lemma (requires less_secret tr x y /\ less_secret tr y z)
          (ensures less_secret tr x z)
  = ()

instance label_labelled : labelled label =
{
  extract_label = fun x -> x
}

instance bytes_labelled {| crypto_usages |} : labelled bytes =
{
  extract_label = get_label
}

instance ps_labelled (a:Type) {| parseable_serializeable bytes a |} {| crypto_usages |}: labelled a =
{
  extract_label = fun x -> get_label (serialize #bytes a x)
}
