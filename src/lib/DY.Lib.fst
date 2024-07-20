module DY.Lib

/// This module groups all the modules of the "lib" DY*,
/// modules built on top of DY.Core that provide more user-friendly API.

/// Integration with Comparse
include DY.Lib.Comparse.Glue
include DY.Lib.Comparse.Parsers

/// The split function methodology
include DY.Lib.SplitFunction

/// Split function methodology for cryptographic invariants
include DY.Lib.Crypto.AEAD.Split
include DY.Lib.Crypto.KdfExpand.Split
include DY.Lib.Crypto.PKE.Split
include DY.Lib.Crypto.Signature.Split

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

/// Functions and lemmas for HPKE, built on top of kem, kdf and aead
include DY.Lib.HPKE

include DY.Lib.Communication
