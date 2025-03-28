module DY.Lib.Comparse.DYUtils

open Comparse
open DY.Core

open DY.Lib.Comparse.Glue
open DY.Lib.Comparse.Parsers

/// This module provides some utility functions for working more simply
/// with parseable bytes (e.g., lifting predicates from abstract types to
/// their serialized bytes counterparts).

#set-options "--fuel 0 --ifuel 0"

unfold
val parse_and_pred:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  (p:a -> Type0) -> (bytes -> Type0)
let parse_and_pred #a p = (fun b ->
  match parse a b with
  | None -> False
  | Some x -> p x
  )
