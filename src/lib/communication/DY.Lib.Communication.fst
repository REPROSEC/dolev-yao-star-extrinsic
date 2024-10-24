module DY.Lib.Communication

// Functions for user to send and receive
// confidential and/or authenticated messages
include DY.Lib.Communication.API

// Predicates that provide the guarantees
// for the higher layer protocols
include DY.Lib.Communication.API.Invariants

// Proof that the API functions fulfill the
// predicates
include DY.Lib.Communication.API.Lemmas
