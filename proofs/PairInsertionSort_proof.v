Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
(* Load the examples CF definitions. *)
Require Import PairInsertionSort_ml.

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

Fixpoint insert (x : int) (l : list int) : list int * list int :=
  match l with
  | nil => (x :: nil, nil)
  | y :: t => if Z_lt_le_dec x y then
                let (hd, tl) := insert x t in
                  (y :: hd, tl)
              else
                (x :: nil, y :: t)
  end.

Definition insert_two (x : int) (y : int) (l : list int) : list int :=
  let (hd, tl) := insert x l in
  let (hd', tl') := insert y tl in
    hd ++ hd' ++ tl'.

Fixpoint sort (l1 : list int) (l2 : list int) : list int :=
  match l2 with
  | nil => l1
  | x :: nil =>
      let (hd, tl) := insert x l1 in
        hd ++ tl
  | x :: y :: l2 =>
      if Z_lt_le_dec x y then
        let l1' := insert_two y x l1 in sort l1' l2
      else
        let l1' := insert_two x y l1 in sort l1' l2
  end.

Definition sort' (l : list int) : list int := rev (sort nil l).

Lemma insert_sorted (x : int) (l : list int) :
 LocallySorted Z.ge l ->
 let (hd, tl) := insert x l in
   (exists hd', hd' & x = hd /\ hd' ++ tl = l) /\
   LocallySorted Z.ge (hd ++ tl).
Proof.
  induction 1; intros; simpls~.
  - splits~. exists~ (@nil int).
  - case_if~.
    + splits~. exists~ (a :: nil).
    + splits~. exists~ (@nil int).
  - case_if~.
    + match goal with
      |- let (_, _) := let (_ , _):= ?t in _ in _ => set t in *
      end.
      destruct p.
      destruct IHLocallySorted as [[hd' IHhd'] IH].
      splits~.
      * exists~ (a :: hd').
        unpack IHhd'; subst.
        splits~.
        now rewrite TEMP0.
      * unpack IHhd'; subst. destruct~ hd'.
        constructor~.
        inversion~ TEMP0.
    + splits~. exists~ (@nil int).
Qed.


Lemma LocallySorted_merge_one (l1 l2 : list int) (x : int) :
  LocallySorted Z.ge (l1 & x) -> LocallySorted Z.ge (x :: l2) ->
  LocallySorted Z.ge (l1 & x ++ l2).
Admitted.

Lemma LocallySorted_app_inv (l1 l2 : list int) :
  LocallySorted Z.ge (l1 ++ l2) ->
  LocallySorted Z.ge l1 /\ LocallySorted Z.ge l2.
Admitted.

Lemma insert_two_sorted (x : int) (y : int) (l : list int) :
  x >= y -> LocallySorted Z.ge l ->
  LocallySorted Z.ge (insert_two x y l).
Proof.
  intros Hxy Hl; unfold insert_two.
  forwards~: insert_sorted x l.
  destruct (insert x l) as [hd tl].
  destruct H as [H1 H2].
  forwards~[Ha Hb]: LocallySorted_app_inv H2.
  forwards~: insert_sorted y tl.
  destruct (insert y tl) as [hd' tl'].
  destruct H as [H H'].
  destruct H. unpack H; subst.
  destruct H1. unpack H; subst.
  apply~ LocallySorted_merge_one.
  destruct~ x0.
  constructor~.
  forwards~[_ ?]: LocallySorted_app_inv H2.
  inversion~ H.
Qed.

Fixpoint sort_sorted (l1 : list int) (l2 : list int) :
  LocallySorted Z.ge l1 ->
  LocallySorted Z.ge (sort l1 l2).
Proof.
  destruct l2; simpls~.
  destruct l2; simpls~; intros.
  - forwards~: insert_sorted z l1.
    destruct (insert z l1).
    now unpack H0.
  - case_if~.
    + forwards~: insert_two_sorted z0 z l1.
    + forwards~: insert_two_sorted z z0 l1.
Qed.

Lemma insert_perm (x : int) (l : list int) :
  let (hd, tl) := insert x l in
  Permutation (x :: l) (hd ++ tl).
Proof.
  induction l; simpls~.
  case_if~.
  destruct~ insert.
Qed.

Lemma insert_two_perm (x : int) (y : int) (l : list int) :
  Permutation (x :: y :: l) (insert_two x y l).
Proof.
  unfold insert_two.
  forwards~: insert_perm x l.
  destruct (insert x l).
  forwards~: insert_perm y l1.
  destruct~ insert.
  rewrite !app_is_app in *.
  rewrite perm_swap.
  rewrite H.
  rewrite <- H0.
  apply~ Permutation_cons_app.
Qed.

Require Import PermSolve.
Module Keys <: WithType.
  Definition A := int.
End Keys.
Module PS := PermutationSolve Keys.

Fixpoint sort_perm (l1 : list int) (l2 : list int) :
  Permutation (l1 ++ l2) (sort l1 l2).
Proof.
  destruct l2; simpl.
  - rew_list. reflexivity.
  - destruct l2; simpls; rew_list in *.
    + forwards: insert_perm z l1.
      destruct insert.
      rewrite <- H.
      rewrite app_is_app.
      PS.solve_perm.
    + case_if~.
      * forwards: insert_two_perm z0 z l1.
        etransitivity; only 2: apply sort_perm.
        rewrite !app_is_app in *.
        rewrite <- H.
        PS.solve_perm.
      * forwards: insert_two_perm z z0 l1.
        etransitivity; only 2: apply sort_perm.
        rewrite !app_is_app in *.
        rewrite <- H.
        PS.solve_perm.
Qed.

Theorem sort'_ok (l : list int) :
  LocallySorted Z.le (sort' l) /\ Permutation l (sort' l).
Proof.
  splits~.
  - unfold sort'.
    forwards~: sort_sorted (@nil int) l.
    admit.
  - unfold sort'.
    forwards~: sort_perm (@nil int) l.
    rewrite !rev_is_rev in *.
    now rewrite <- Permutation_rev.
Qed.