# Formal Security Analysis of the ISO-DH Protocol

This folder contains a formal security analysis
of the Diffie-Hellman key exchange protocol with 
digital signatures based on the [ISO/IEC 9798-3:2019(E)](https://www.iso.org/standard/67115.html) 
standard. In this analysis, we prove the following 
properties of the ISO-DH protocol:

1. Mutual authentication
2. Forward secrecy of the key ``k`` 
  (as long as the private DH keys are secret, 
  the key ``k`` does not leak)

**Protocol Flow**

```
A -> B: {A, gx}                            msg1
B -> A: {B, gy, sign({A; gx; gy}, privB)}  msg2
A -> B: {sign({B; gx; gy}, privA)}         msg3
```

The model of the protocol is split into two
parts. The first part is in the ``DY.Example.DH.Protocol.Total``
module which contains all the code that does
not depend on the trace, e.g., message definitions,
cryptographic functions, and message encoding.
The second part is in the ``DY.Example.DH.Protocol.Stateful`` 
module, containing the logic that depends on the
trace, e.g., state definitions, state encoding, and sending messages.

Since the model is split into two parts, the proof is also
split into the two modules ``DY.Example.DH.Protocol.Total.Proof``
and ``DY.Example.DH.Protocol.Stateful.Proof``. The first
module contains helper lemmas about the total functions 
used in the stateful proof to prove that every
stateful function fulfills the trace invariants.

The module ``DY.Example.DH.SecurityProperties`` formalizes the
above-mentioned security properties and proves them with the
protocol invariants.

To see whether the protocol has been modeled correctly the module
``DY.Example.DH.Debug`` provides an implementation of an honest
protocol run. This module can be extracted to OCaml code to
print an example trace to the console.
The module ``DY.Example.DH.Debug.Proof`` proves that the
honest protocol run fulfills the protocol invariants.
This proof serves as a sanity check for the protocol invariants.

## Check and Run the Model
To verify the F* code you can call ``make`` from either this 
directory or the repository's root directory.
To run the ``DY.Example.DH.Debug`` module you have to
execute ``make test`` from this directory.
