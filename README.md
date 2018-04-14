# CFML skeleton: startup project using CFML

## Structure of the project

- OCaml code to be verified goes into `src/`;
- For each .ml file `src/foo.ml`, CFML will generate a `Foo_ml.v` Coq file
  containing the corresponding characteristic formulae;
- The proofs for `src/foo.ml` should be written in `proofs/Foo_proofs.v`; this
  file should `Require Import Foo_ml.` to load the characteristic formulae.

## Adding a new .ml file

To add a new `src/bar.ml` file:
- add `bar.native` to `OCAMLBUILD_TARGETS` in `src/Makefile`
- add `bar.ml` to `SOURCES` in `proofs/Makefile`
- create `proofs/Bar_proof.v` with prelude:

```coq
Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
(* Load the CF definitions. *)
Require Import Bar_ml.
```
