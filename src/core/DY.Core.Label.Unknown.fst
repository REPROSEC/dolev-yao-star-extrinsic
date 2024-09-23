module DY.Core.Label.Unknown

/// The unknown label is in reality public (i.e. always corrupt).
/// However we can't reason on it because it's hidden behind an interface file,
/// unless we `friend DY.Core.Label.Unknown`, which we shouldn't do.

let unknown_label = {
  is_corrupt = (fun tr -> True);
  is_corrupt_later = (fun tr ev -> ());
}
