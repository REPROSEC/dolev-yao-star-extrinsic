module DY.Lib.Labelled

open Comparse
open DY.Lib.Comparse.Glue
open DY.Core

(**
  The idea of this typeclasss is that we often want to reason about the secrecy of some value (or label)
  by tracing through a series of can_flow relations. However, often, these are not simple label-label connections,
  or bytes-label connections (captured by, for instance, is_knowable_by), but some mix --- for instance, we might
  want to say that the label of an access token can flow to the label of a password, or that the label of some
  encrypted message can flow to the label of the encryption key.

  It is moderately inconvenient to have to call get_label all over the place when working with labelled bytes, and
  even more so when dealing with the label of some more complex structure, such as a message (hence the utility of
  predicates such as is_knowable_by and is_secret).

  By making this generic, we can use the less_secret function (or variants thereof) to work through these chains of
  reasoning without needing to worry about explicitly getting the labels of the various data we want to connect, thus
  focusing the proof on the core ideas.

  From some initial testing, this seems to work fine, but I don't find instances in the existing examples where it makes
  a substantial difference, probably because simple examples leverage is_knowable_by quite well.

  I think this exact implementation may not be final, but that the idea here is worth looking into incorporating (maybe
  even into the core, at least for the label and bytes instances).
*)
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
