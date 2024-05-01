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

## How to contribute

Please read the [CONTRIBUTING](CONTRIBUTING.md) document.