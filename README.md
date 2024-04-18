# DY\*, proof of concept with extrinsic proofs

## What is in this repository

### The "core" DY\*

In the namespace [`DY.Core`](src/core/DY.Core.fst),
we can find all functions and theorems needed to specify a cryptographic protocol and prove its security.
To read and understand this module, you can start by reading the file [`DY.Core.fst`](src/core/DY.Core.fst).

### The "lib" DY\*

To improve the user experience of specifying cryptographic protocols and doing security proofs,
we can find functions and theorems built on top of [`DY.Core`](src/core/DY.Core.fst) in [`DY.Lib`](src/lib/DY.Lib.fst).

### Examples

The NSL protocol is proved secure in the namespace [`DY.Example.NSL`](examples/nsl_pk/DY.Example.NSL.SecurityProperties.fst).

## How to build

### Dependencies

DY\* depends on the F\* proof-oriented programming language,
and depend on [Comparse](https://github.com/TWal/comparse), a library for message formats in F\*.

Two choices are possible:
- either [Comparse](https://github.com/TWal/comparse) is cloned in `../comparse`
  and `fstar.exe` is in the `PATH`
- or [Comparse](https://github.com/TWal/comparse) is cloned in `COMPARSE_HOME`
  and F\* in `FSTAR_HOME`,
  in that case using [direnv](https://direnv.net/) is a advisable.

### Compiling

Running `make` will compile and verify DY\* and its examples.

## Differences with DY\* with intrinsic proofs

### Structure for DY\*-style proofs

To understand the proof engineering decisions behind DY\*,
we must first understand how DY\* proofs are structured.

DY\* proofs proceed in the following steps:
1. define global protocol invariants
2. prove that every step of the protocol preserve these invariants
3. prove that the protocol invariants imply the security property you want

The first step is usually where lies the intuition on why the protocol is secure.
Finding the right invariants usually require back-and-forth until finding the right ones.

The second step is usually pedestrian,
and works by proving that all sub-steps of a given protocol step preserve the invariants.

The last step is usually straightforward,
as the protocol invariants are stronger versions of the security properties.

### Fundamental design differences

First, let's dive into the design decisions of this DY\* version that are fundamentally different than in the original DY\*,
hence justify a rewrite instead of an iteration on the DY\* code.

#### Extrinsic proofs

The fundamental design difference is in proving that every protocol step preserve the global protocol invariants.
The approach chosen in the original DY\* is to do proofs in the "intrinsic" style,
meaning that the functions are proved to preserve the invariants at the same time they are defined.
This means that we can call them only when some preconditions are satisfied (e.g. all the inputs satisfy the invariants),
and gives back some post-condition (e.g. the output satisfy the invariants).

This style has a few benefits:
- when the proofs are simple enough,
  the SMT do most of the work and little proof annotation are needed
- it ensures that every function is proved to preserve the invariants

However, it also comes with some downsides.
- Mixing protocol definition and proofs makes the protocol definition hard to read.
  This is a concern, because the protocol definition is part of the TCB:
  it must be readable to ensure we prove the security properties on the right protocol,
  and not some subtle variation on it.
- Supporting the concrete execution of the protocol requires to have `admit`s somewhere.
  Indeed, all the cryptographic functions comes with security theorems about them,
  for example, the hash function is collision-free.
  While this property is true in the symbolic model, it is false in the concrete model.
  Indeed, hash-functions are collision-resistant but not collision-free:
  it is hard to compute collision, although they do exist (by a simple pigeon-hole argument).

This DY\* is an attempt to see how we could design DY\* with extrinsic proofs in mind.
- We can completely separate the protocol definition and its security proof,
  making it much easier to review.
- We can implement concrete execution without any `admit`s:
  by writing the protocol specification using a typeclass.
  Then, we can instantiate the typeclass concretely to execute it,
  and instantiate the typeclass with DY\* to do security proofs.

As a consequence of this design decision, other fundamental design differences with the original DY\* follow.

#### Lightweight monad

The original DY\* use an effect to define and prove stateful code, i.e. code that modify the trace,
by sending messages on the network, storing data or triggering protocol events.

This works great when doing intrinsic proofs because F\*'s effects are designed for that.
It is not possible to do extrinsic proofs on F\*'s effects, because they can't be reified.

Instead, we write stateful protocol code in a lightweight state monad.

#### Explicit trace

The original DY\* use the witness mechanism to have an implicit and global trace that can be used by various predicates.
The predicate usually depend on a timestamp that is used to refer to a particular event of the trace or a particular prefix of the trace.

The witness mechanism is sound only when using F\*'s effect system,
hence this is not an option when working in a lightweight monad.

Instead of the timestamp, the various security predicate depend on an explicit trace.
With carefully designed SMT patterns, we have no problem with proofs that rely on the monotonicity of predicates (w.r.t. the trace).

This in itself can also be seen as an improvement:
the witness mechanism is unique to F\*, and it is hard to understand for users of other proof assistants.
The approach with explicit trace could be implemented in any proof assistant,
hence it makes the DY\* approach more understandable by users of other proof assistants.

### Secondary design differences

These design differences could be backported in the original DY\* if needed.

#### Split predicate methodology

DY\* proofs rely on global protocol invariants (e.g. what protocol participants are allowed to store, or are allowed to sign),
that must be preserved by each step of the protocol.
The practice of defining this global protocol invariant monolithically somewhere has a few drawbacks:
- it does not allows the user to do modular proofs, as many unrelated predicates are put in the same place
- when modifying the global predicate for some sub-component, other unrelated sub-components will need to be re-checked (and their proof might fail if the SMT gods are angry!)
- it make it difficult to create reusable components (such as a generic state to store private keys)

We implement and use a library to create a global predicate from several independent local predicates,
defined in `DY.Lib.SplitPredicate`.
Then, instead of implementing functions that use a top-level-defined global predicate,
functions take as parameter the global predicate,
with the precondition that it contains some top-level-defined local predicate.

#### Clean separation between core DY\* and helper library

The core DY\* library, in the namespace `DY.Core` try to go to the essence of DY\*, such as:
- bytes definition (`DY.Core.Bytes.Type`) and cryptographic functions (`DY.Core.Bytes`)
- stateful functions (`DY.Core.Trace.Type`)
- labels (`DY.Core.Label`), invariants (`DY.Core.Trace.Invariant`)
- attacker knowledge (`DY.Core.Attacker.Knowledge`)

This is the TCB of DY\*,
the part that need to be reviewed when trying to understand what is proved by DY\*.

It is by itself not user-friendly, hence we define many helpers in `DY.Lib`, such as:
- integration with Comparse (`DY.Lib.Comparse.Glue`)
- typed and split API for state management (`DY.Lib.State.Typed`) and event triggering (`DY.Lib.Event.Typed`)
- state helpers, such as creating a state that contains maps (`DY.Lib.State.Map`)
- state to manage a local PKI (`DY.Lib.State.PKI`) and private keys (`DY.Lib.State.PrivateKeys`)

These helpers are used extensively in the examples,
in fact the low-level functions to store state or trigger event is never used in the examples.

#### Clean separation between pure and stateful code in the examples

To improve readability of examples, we separate them in two parts:
- the pure code of the protocol,
- the stateful code of the protocol, that is in charge of plugging the pure code with the outside world
  (by sending and receiving messages on the network, retrieving and storing state, etc).

This helps with protocol executability,
because only the pure part of the code can be executed concretely.
Indeed, the stateful part of the protocol with the global trace is a model artifact that cannot be executed.

Furthermore, the interesting part a protocol specification (hence the difficult part of the proof) lies in the pure code.
The size of the stateful code is expected to be small regardless of the protocol complexity,
as it is only boilerplate code that connects it to the outside world.

#### Global protocol invariants as a typeclass

Every predicate and theorem of DY\* depend on the global protocol invariants,
hence take it as a parameter.
The situation is in fact worse:
each predicate depend on some subset of the global protocol invariants,
as this predicate can be used to define other protocol invariants
(e.g. the state invariant definition may use `is_publishable`, that depend on other invariants).

To remove this friction in DY\* proofs,
we use F\*'s typeclass mechanism to infer the correct value for protocol invariants.
This works because there is always at most one global protocol invariant in the scope.

#### Renaming

Some predicates and types are renamed with more explicit names.
- `is_valid` becomes `bytes_invariant`
- `is_publishable` keeps its name
- `is_msg` becomes `is_knowable_by`
- `key_usages` becomes `crypto_usages`
- `usage_preds` becomes `crypto_predicates`
- `global_usages` becomes `crypto_invariants`
- `trace_preds` becomes `trace_invariants`
- `preds` becomes `protocol_invariants`
