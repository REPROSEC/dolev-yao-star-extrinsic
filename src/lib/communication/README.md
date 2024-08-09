# Communication Layer

This layer provides functions to send and receive confidential
and/or authenticated messages. For each function the layer provides
proofs of certain predicates that are guaranteed by the respective
cryptographic primitive. The preconditions for the functions can be
extended via the `comm_higher_layer_event_preds` type. This layer provides the following functionalities (unchecked boxes are work in progress):

- [x] Confidential send and receive functions
- [x] Authenticated send and receive functions
- [ ] Confidential and authenticated send and receive functions
- [ ] Response-request pair send and receive functions

## Overview

The module `DY.Lib.Communication.API` provides the functional
code to send and receive messages but does not give any
security guarantees.
The module `DY.Lib.Communication.API.Predicates` contains
the cryptographic predicates and event predicates that have
to be included in the user's code to get the security guarantees from
the communication layer. These predicates are combined with the
user's predicates via the [split predicates methodology](../utils/DY.Lib.SplitFunction.fst)
used in DY*.
The final module is `DY.Lib.Communication.API.Lemmas`, which proves
that the predicates hold for the respective functions. These proofs
are used by the user to prove security properties about the send and
receive functions.
Examples for how to use the communication layer functions
in a higher layer protocol can be found in this [repository]().
