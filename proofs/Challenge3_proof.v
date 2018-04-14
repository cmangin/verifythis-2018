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

Ltac auto_tilde ::= (* try unfold LibListZ.length in *;  *)rew_list in *; eauto with maths.


Parameter ro : hprop -> hprop.

Hypothesis ro_of_full : forall H,
  H ==> H \* ro H.

Parameter get_spec_ro :
  curried 2%nat Array_ml.get /\
  forall A `{Inhab A} (xs:list A) t i,
  index xs i ->
  app Array_ml.get [t i]
    INV (ro (t ~> Array xs))
    POST \[= xs[i] ].

Definition I (a : array bool) :=
  Hexists L,
    ro (a ~> Array L) \*
    If (Exists is_true L) then a ~> Array L else \[].

(* not usable since this requires full owneship over next *)
Lemma fetch_and_add_spec : forall rnext next,
  app fetch_and_add [rnext]
    PRE (rnext ~~> next)
    POST (fun x => rnext ~~> (next + 1) \* \[ x = next ]).
Proof. introv. xcf. xapps. xapps. xrets~. Qed.

Lemma abql_release_spec : forall (n:int) pass (ticket:int),
  0 < n ->
  app abql_release [n pass ticket]
    PRE (pass ~> Array (make n false))
    POST (fun (tt:unit) => I pass).
Proof.
  introv. xcf.
  xapps~. xapps. { admit. }
  hsimpl. unfold I.
  hsimpl ((make n false)[ticket + 1 `mod` n:=true]).
  assert (Exists is_true (make n false)[ticket + 1 `mod` n:=true]).
  { admit. }
  case_if~. xchange ro_of_full. hsimpl. hsimpl.
Qed.
