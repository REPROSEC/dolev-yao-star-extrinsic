module DY.Core.Label.Unknown

open DY.Core.Label.Type

/// In some functions or proofs, we may need a label which can be arbitrary:
/// its value doesn't matter, we just need a label,
/// and its value doesn't impact the proofs,
/// as in `DY.Core.Bytes.get_label` when the `bytes` is ill-formed.
/// Instead of having to choose an arbitrary label,
/// we can use the following `unknown_label`
/// on which we can't reason because it's hidden behind an interface file.
/// This helps to justify that the proofs don't rely on the actual value of the label.

[@@ must_erase_for_extraction]
val unknown_label: label
