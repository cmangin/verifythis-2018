Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
Require Import CFML.Stdlib.Array_proof CFML.Stdlib.Pervasives_proof.
Require Import TLC.LibListZ.
(* Load the examples CF definitions. *)
Require Import PairInsertionSort_funs_ml.

Require Import Permutation.
Hint Constructors Permutation.
Hint Constructors Forall.
Ltac auto_tilde ::= rew_list in *; eauto with maths.

Definition sorted (l : list int) :=
  forall i, 0 <= i -> i < length l - 1 -> l[i] <= l[i+1].

Lemma insert_spec : forall al jr
  (l1 h l2 : list int) (x : int) (j : int) (shift : int),
  app insert [al x jr shift]
    PRE (al ~> Array (l1 ++ h ++ l2) \* jr ~~> j \*
         \[ shift > 0 /\ length l1 = j + 1 /\ length h = shift /\ sorted l1 ])
    POST (fun (t : unit) =>
      Hexists l1a h' l1b j',
      al ~> Array (l1a ++ h' ++ x :: l1b ++ l2) \* jr ~~> j' \*
      \[ length l1a = j' + 1 /\ length h' = shift - 1 /\ l1a ++ l1b = l1 /\
         sorted (l1a ++ x :: l1b)]).
Proof.
  introv.
  xcf.
  xpull; intros; unpack.
  xwhile_inv_basic (fun (b : bool) (m : int) =>
    Hexists l1a h' l1b,
      al ~> Array (l1a ++ h' ++ l1b ++ l2) \*
      jr ~~> m \*
      \[ m + 1 = length l1a /\
         length h' = shift /\
         l1 = l1a ++ l1b /\
         Forall (fun z => z > x) l1b /\
         b = isTrue (m >= 0 /\ l1a[m] > x) ]) (downto (-1)).
  - hsimpl (>> __ j l1 h (@nil int)).
    splits~.
  - intros b m.
    xpull.
    intros l1a h' l1b ?.
    unpack.
    xapps.
    xand.
    + xapps. xapps.
      { apply~ index_of_inbound. }
      xrets.
      splits~.
      rewrite~ read_app.
      assert (m < length l1a) by math.
      case_if~. splits~.
    + xsimpl. splits~.
  - intros m. xpull.
    intros l1a h' l1b ?.
    unpack.
    xapps. xapps.
    { apply~ index_of_inbound. }
    xapps. xapps.
    { apply~ index_of_inbound. }
    xapps.
    rew_bool_eq in *. unpack.
    forwards~[y [l1a' ->]]: (length_pos_inv_last l1a).
    forwards~[s [hs ->]]: (length_pos_inv_last h').
    xsimpl~ __ (m - 1) l1a' (y :: hs) (y :: l1b).
    { rewrite~ read_middle.
      rewrite update_app_r with (i := m) (j := shift); auto_tilde.
      rewrite~ update_cons_pos.
      rewrite update_app_r with (i := shift - 1) (j := 0); auto_tilde.
      rewrite~ update_zero. }
    splits~. constructor~.
    rewrite~ read_middle in H8.
  - intros m l1a h' l1b ?.
    unpack.
    xapps.
    xapps.
    { apply~ index_of_inbound. }
    forwards~[s [hs ->]]: (length_pos_inv_last h').
    xsimpl~ l1a hs l1b m.
    { rewrite update_app_r with (i := m + 1) (j := shift - 1); auto_tilde.
      rewrite update_app_r with (i := shift -1) (j := 0); auto_tilde.
      rewrite ~ update_zero. }
    splits~.
    admit.
Qed.

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
       b = isTrue (m > 1) ]
  ).
  - hsimpl __ (@nil int) L.
    splits~. admit. (* nil is sorted *)
  - intros b m.
    xpull.
    intros l1 l2 i ?.
    unpack.
    xapps.
    xapps.
    xrets.
    splits~.
    splits~.
  - intros m.
    xpull. intros l1 l2 i ?.
    unpack.
    xapps. xapps.
    { apply~ index_of_inbound. }
    xapps. xapps. xapps.
    { apply~ index_of_inbound. }
    xapps. xapps. xapps.
    rew_bool_eq in H3.
    destruct l2 as [ | x1 [ | x2 l2]];
    try solve [false~; math].
    rewrite~ read_middle.
    assert ((l1 ++ x1 :: x2 :: l2)[i + 1] = x2) as ->.
    { rewrite~ read_app.
      case_if~. rewrite~ read_cons_case.
      case_if~. rewrite~ read_cons_case.
      case_if~. }
    xseq (ir ~~> i \* a ~> Array (l1 ++ x1 :: x2 :: l2) \*
      Hexists xv yv, x ~~> xv \* y ~~> yv \* \[yv <= xv /\
      Permutation (xv :: yv :: nil) (x1 :: x2 :: nil)]).
    { xif.
      - xapps. xapps. xapps. xapps.
        xsimpl~.
      - xrets~. }
    intros xv yv Hxy.
    xapps. xapps. xapps.

    xapp_spec~ insert_spec (>> __ (x1 :: x2 :: nil)).
    intros l1a h' l1b j' ?.
    unpack.
    assert (length h' = 1) by auto_tilde; clear H5.
    xapps.

    xapp_spec~ insert_spec (>> l1a h' (xv :: l1b ++ l2)).
    { splits~. admit. }
    intros l1a' h'' l1b' j'' ?.
    unpack.
    assert (h'' = nil) as -> by apply~ length_zero_inv; clear H11.

    xapps. xapps.
    xsimpl~ __ (m - 2) (l1a' ++ yv :: l1b' ++ xv :: l1b) l2.
    subst~.
    splits~.
    + admit.
    + admit.
  - intros m l1 l2 i ?.
    unpack.
    xapps. xapps. xrets.
    xif.
    + xapps. xapps.
      { apply~ index_of_inbound. }
      xapps. xapps.
      destruct l2 as [ | x [ | ]]; try solve [false~; math].
      rewrite~ read_last_case.
      case_if~.

      xapp_spec~ insert_spec (>> __ (x :: nil)).
      xpull.
      intros l1a h l1b j' ?.
      unpack.
      xsimpl~.
      assert (h = nil) as -> by apply~ length_zero_inv.
      splits~.
      admit.
    + xrets.
      assert (l2 = nil) as -> by apply~ length_zero_inv.
      splits~.
Qed.