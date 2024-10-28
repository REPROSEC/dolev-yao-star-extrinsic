module DY.Core.Label.Unknown

/// The unknown label is in reality public (i.e. always corrupt).
/// However we can't reason on it because it's hidden behind an interface file,
/// unless we `friend DY.Core.Label.Unknown`, which we shouldn't do.

let unknown_label = {
  is_corrupt = FStar.FunctionalExtensionality.on _ (fun tr ->
    True <: prop
  );
  is_corrupt_later = (
    reveal_opaque (`%is_monotonic) is_monotonic
  );
}
