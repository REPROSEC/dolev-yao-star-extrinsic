module DY.Lib.Communication

// Data types for the communication layer
include DY.Lib.Communication.Data

// Functions for user to send and receive confidential and/or authenticated
// messages
include DY.Lib.Communication.Core

// Invariants that provide the guarantees for the higher layer protocols
include DY.Lib.Communication.Core.Invariants

// Proof that the core functions fulfill the invariants
include DY.Lib.Communication.Core.Lemmas

// Properties that can be proven from the communication layer invariants
include DY.Lib.Communication.Core.Properties

// Functions for user to send and receive request-response pairs. This code
// depends on functions from the Core module.
include DY.Lib.Communication.RequestResponse

// Invariants that provide the guarantees for the higher layer protocols
include DY.Lib.Communication.RequestResponse.Invariants

// Proof that the request-response functions fulfill the invariants
include DY.Lib.Communication.RequestResponse.Lemmas

// Properties that can be proven from the request-response invariants
include DY.Lib.Communication.RequestResponse.Properties

// Functions to nicely print messages, events and states from the communication
// layer
include DY.Lib.Communication.Printing
