# Communication Layer

This layer provides functions to send and receive confidential and/or
authenticated messages. For each function the layer provides proofs of certain
predicates that are guaranteed by the respective cryptographic primitive. The
preconditions for the functions can be extended via the
`comm_higher_layer_event_preds` type for the core functions and via the
`comm_reqres_higher_layer_event_preds` type for the request-response pair
functions. This layer provides the following functionalities:

- Confidential send and receive functions
- Authenticated send and receive functions
- Confidential and authenticated send and receive functions
- Response-request pair send and receive functions

## Overview

The communication layer can be divided into the core functions that send a
single message from a sender to a receiver and the functions that can send and
receive request-response pairs.

The module `DY.Lib.Communication.Core` provides the functional code to send and
receive messages but does not give any security guarantees. The module
`DY.Lib.Communication.Core.Invariants` contains the cryptographic predicates and
event predicates that have to be included in the user's code to get the security
guarantees from the communication layer. These predicates are combined with the
user's predicates via the [split predicates
methodology](../utils/DY.Lib.SplitFunction.fst) used in DY*. The invariants are
proven for every function in the `DY.Lib.Communication.Core.Lemmas` module.
These proofs are used by the user to prove security properties about the send
and receive functions.

The request-response pairs are implemented with the same structure in the
`DY.Lib.Communication.RequstResponse.*` namespace.

Examples for how to use the communication layer functions
in a higher layer protocol can be found in this [repository](https://github.com/fabian-hk/dolev-yao-star-communication-layer-examples).
