Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
(* Load the examples CF definitions. *)
Require Import Challenge1_ml.

Require Import TLC.LibInt TLC.LibTactics.
Require Import TLC.LibListZ.
Require Import TLC.LibWf.
Require Import Sorting Permutation.

Open Scope Z_scope.

Hint Constructors LocallySorted.
Hint Constructors Permutation.
Ltac auto_tilde ::= rew_list in *; eauto with maths.

Lemma app_is_app : LibList.app = List.app.
Admitted.
Lemma rev_is_rev : rev = List.rev.
Admitted.
