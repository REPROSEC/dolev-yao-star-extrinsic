module DY.Lib

/// This module groups all the modules of the "lib" DY*,
/// modules built on top of DY.Core that provide more user-friendly API.

/// Integration with Comparse
include DY.Lib.Comparse.Glue
include DY.Lib.Comparse.Parsers

/// The split predicate methodology
include DY.Lib.SplitPredicate

/// User-friendly event API
include DY.Lib.Event.Typed

/// User-friendly state API
include DY.Lib.State.Tagged
include DY.Lib.State.Typed

/// Various state helpers
include DY.Lib.State.Map
include DY.Lib.State.PKI
include DY.Lib.State.PrivateKeys

/// Provide functions to print the trace
include DY.Lib.Printing
