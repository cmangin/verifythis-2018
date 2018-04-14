Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
(* Load the examples CF definitions. *)
Require Import CFML.Stdlib.Array_proof.
Require Import CFML.Stdlib.Pervasives_proof.
Require Import Challenge2_ml.

Require Import TLC.LibInt TLC.LibTactics.
Require Import TLC.LibList TLC.LibListZ .
Require Import TLC.LibWf.
Require Import Sorting Permutation.

Open Scope Z_scope.

Hint Constructors LocallySorted.
Hint Constructors Permutation.
Ltac auto_tilde ::= try unfold LibListZ.length in *; rew_list in *; eauto with maths.

Inductive color := R | B.
Definition coloring := list color.

(* Z_lt_le_dec: forall x y : int, {x < y} + {y <= x} *)

Fixpoint coloring_valid (aux: int) (c : coloring) : bool :=
  match c with
  | B :: cs => if Z_lt_le_dec aux 3 then false else coloring_valid 0 cs
  | R :: cs => coloring_valid (aux + 1) cs
  | nil => if Z_lt_le_dec aux 3 then false else true
  end.

Definition invariant (n: int) (counts: list int) (colorings: list coloring) :=
  length counts = n /\
  length colorings = n /\
  forall i, 0 <= i < n ->
    counts[i] = length colorings[i] /\
    Forall (fun c => length c = i) colorings.

Lemma docount_spec : forall (a:loc) (L: list int),
  app docount [count a]
    PRE (a ~> Array L)
    POST (fun (tt:unit) =>
            Hexists L' C,
            a ~> Array L' \* \[ invariant (length L') L' C ]).
Proof.
Admitted.