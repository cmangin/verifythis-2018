Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
(* Load the examples CF definitions. *)
Require Import CFML.Stdlib.Array_proof.
Require Import CFML.Stdlib.Pervasives_proof.
Require Import Challenge3_ml.

Require Import TLC.LibInt TLC.LibTactics.
Require Import TLC.LibList TLC.LibListZ .
Require Import TLC.LibWf.
Require Import Sorting Permutation.

Open Scope Z_scope.

Hint Constructors LocallySorted.
Hint Constructors Permutation.
Ltac auto_tilde ::= (* try unfold LibListZ.length in *;  *)rew_list in *; eauto with maths.

