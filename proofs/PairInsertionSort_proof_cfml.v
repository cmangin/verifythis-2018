Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
Require Import CFML.Stdlib.Array_proof CFML.Stdlib.Pervasives_proof.
Require Import TLC.LibListZ.
(* Load the examples CF definitions. *)
Require Import PairInsertionSort_ml.

Require Import Permutation.
Hint Constructors Permutation.
Hint Constructors Forall.
Ltac auto_tilde ::= rew_list in *; eauto with maths.

Definition sorted (l : list int) :=
  forall i, 0 <= i -> i < length l - 1 -> l[i] <= l[i+1].

Lemma sort_spec : forall a (L : list int),
  app sort [a]
    PRE (a ~> Array L)
    POST (fun (t : unit) => Hexists L', a ~> Array L' \* \[sorted L' /\ Permutation L L']).
Proof.
  introv.
  xcf.
  xapp as ir.
  xwhile_inv_basic_measure (fun (b:bool) (m:int) =>
    Hexists L1 L2 i,
    a ~> Array (L1 ++ L2) \*
    ir ~~> i \*
    \[ m = length L2 /\ length L1 = i /\ sorted L1 /\ Permutation L (L1 ++ L2) /\
       if b then True else m <= 1 ]
  ).
  - hsimpl true (@nil int) L.
    splits~. red.
    intros. rew_list in *. math.
  - intros.
    xpull.
    intros.
    xapps.
    xapps.
    xrets.
    unpack H; subst.
    splits~.
    case_if~.
  - admit.
  - intros m l1 l2 i H.
    unpack H; subst.
    xapps.
    xapps.
    xrets.
    xif.
    + xapps.
      xapp as y.
      { apply~ index_of_inbound. }
      intros Hy.
      assert (l2 = y :: nil).
      { destruct~ l2.
        - math.
        - f_equal.
          rew_list in *.
          + rewrite~ read_middle in Hy.
          + apply~ length_zero_inv. }
      xapps.
      xapp as jr.
      xgc (ir ~~> length l1).
      xwhile_inv_basic (fun (b':bool) (m':int) =>
        Hexists L1a h L1b L2t,
          a ~> Array (L1a ++ h :: L1b ++ L2t) \*
          jr ~~> m' \*
          \[ m' + 1 = length L1a /\
             l2 = y :: L2t /\
             l1 = L1a ++ L1b /\
             Forall (fun z => z > y) L1b /\
             b' = isTrue ((m' >= 0) /\ (L1a[m'] > y)) ]) (downto (-1)).
(*             if b' then m' >= 0 else Forall (fun z => z <= y) L1a ]).*)
      * hsimpl (>> __ l1 y __ (@nil int)).
        { subst l2. rew_list~. }
        splits~.
      * intros b' m'. xpull.
        intros ? ? ? ? H0.
        xapps.
        xands.
        -- xapps.
           xapps.
           { apply~ index_of_inbound. }
           xrets.
           unpack H0.
           splits~.
           rewrite read_app.
           assert (m' < length x) by math.
           case_if~.
           splits~.
        -- unpack. splits~.
      * intros m'.
        xpull.
        intros ? ? ? ? H0.
        unpack H0.
        xapps.
        xapps.
        { apply~ index_of_inbound. }
        xapps.
        xapps.
        { apply~ index_of_inbound. }
        xapps.
        rew_bool_eq in *.
        forwards~Hx: (length_pos_inv_last x).
        destruct Hx as [y' [x' Hx]].
        hsimpl (>> __ (m' - 1) x' y' (y' :: x1) (@nil int)).
        { subst l2. rew_list~ in *.
          rewrite read_app.
          assert (m' < length x) by math.
          case_if~. subst x.
          rewrite~ update_middle.
          rewrite read_last_case.
          assert (m' = length x') by math.
          case_if~.
          inversion~ TEMP3. }
        -- subst x. splits~.
           unpack.
           rewrite read_last_case in H1.
           case_if~ in H1.
        -- math.
      * intros. unpack.
        xapps. xapps.
        { apply~ index_of_inbound. }
        hsimpl.
        subst l1 l2.
        inversion H1; subst.
        rew_list in *.
        rewrite~ update_middle.
        assert (x0[x] <= y).
        { admit. }
        admit.
    + xrets.
      assert (l2 = nil) as -> by apply~ length_zero_inv.
      rew_list~.
Qed.




















