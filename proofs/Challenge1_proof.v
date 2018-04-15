Set Implicit Arguments.
(* Load the CFML library. *)
Require Import CFML.CFLib.
(* Load the examples CF definitions. *)
Require Import CFML.Stdlib.Array_proof.
Require Import CFML.Stdlib.Pervasives_proof.
Require Import Challenge1_ml.

Require Import TLC.LibList TLC.LibListZ.

Open Scope Z_scope.

Ltac auto_tilde ::= try unfold LibListZ.length in *; rew_list in *; eauto with maths.

Definition Buf (L1 L2 : list int) gap b :=
  Hexists l r Ljunk buf,
    b ~> `{ buf' := buf;
            l' := (l:int);
            r' := (r:int) } \*
    buf ~> Array (rev L1 ++ Ljunk ++ L2) \*
    \[
      length L1 = l /\
      length Ljunk = gap /\
      r = l + gap
    ].

Definition Buf' (L : list int) (pos : int) b :=
  Hexists L1 L2 gap,
    b ~> Buf L1 L2 gap \*
    \[
      L = rev L1 ++ L2 /\
      pos = length L1
    ].

Lemma Buf_open : forall b L1 L2 gap,
  b ~> Buf L1 L2 gap ==>
  Hexists l r Ljunk buf,
    b ~> `{ buf' := buf;
            l' := (l:int);
            r' := (r:int) } \*
    buf ~> Array (rev L1 ++ Ljunk ++ L2) \*
    \[
      length L1 = l /\
      length Ljunk = gap /\
      r = l + gap
    ].
Proof using. intros. xunfolds~ Buf. Qed.

Lemma Buf_close : forall b gap Ljunk L1 L2 buf l r L,
  length L1 = l ->
  length Ljunk = gap ->
  r = l + gap ->
  L = rev L1 ++ Ljunk ++ L2 ->
  buf ~> Array L \*
  b ~> `{ buf' := buf;
          l' := (l:int);
          r' := (r:int) } ==>
  b ~> Buf L1 L2 gap.
Proof using. intros. xunfolds~ Buf. Qed.

Implicit Arguments Buf_close [].

Hint Extern 1 (RegisterOpen (Buf _ _ _)) =>
  Provide Buf_open.
Hint Extern 1 (RegisterClose (record_repr _)) =>
  Provide Buf_close.

Lemma left_spec : forall b L1 L2 gap,
  app left [b]
    PRE (b ~> Buf L1 L2 gap)
    POST (fun (tt:unit) =>
      match L1 with
      | nil => b ~> Buf L1 L2 gap
      | x :: L1' => b ~> Buf L1' (x :: L2) gap
      end
    ).
Proof.
  intros. xcf.
  xopen b. xpull. intros l r Ljunk buf. intros (? & ? & ?).
  xapps. xrets. xif; swap 1 2.
  { xret. destruct L1. { xclose~ b. } false~. math. }
  { xapps. xapps. xapps. xapps. xapps. xapps. xapps.
    { apply~ index_of_inbound. }
    xapps. xapps. xapps.
    { apply~ index_of_inbound. }
    destruct L1. { false~. }
    destruct (last_case Ljunk) as [|HH].
    { subst Ljunk.
      xchange~ (Buf_close b gap); auto_tilde.
      rewrite~ read_middle. rewrite~ update_middle. }
    { destruct HH as (j & Ljunk' & ?). subst Ljunk.
      xchange~ (Buf_close b gap (z :: Ljunk')); auto_tilde.
      rewrite~ read_middle.
      transitivity (((rev L1 ++ z :: Ljunk') ++ j :: L2)[(r - 1)%I:=z]).
      { auto_tilde. }
      rewrite~ update_middle. }}
Qed.

Lemma left_spec' : forall b L pos,
  app left [b]
    PRE (b ~> Buf' L pos)
    POST (fun (tt:unit) =>
      If pos > 0 then b ~> Buf' L (pos - 1) else b ~> Buf' L pos).
Proof.
  introv. unfold hdata.
  unfold Buf'. xpull. intros L1 L2 gap (? & ?).
  destruct~ L1.
  { case_if~. { false. math. } xapply~ left_spec. }
  { case_if~; swap 1 2. { false~. } xapply~ left_spec. }
Qed.

Lemma right_spec : forall b L1 L2 gap,
  app right [b]
    PRE (b ~> Buf L1 L2 gap)
    POST (fun (tt:unit) =>
      match L2 with
      | nil => b ~> Buf L1 L2 gap
      | x :: L2' => b ~> Buf (x :: L1) L2' gap
      end
    ).
Proof.
  intros. xcf.
  xopen b. xpull. intros l r Ljunk buf. intros (? & ? & ?).
  xapps. xapps. xapps. xrets. xif; swap 1 2.
  { xret. destruct L2. { xclose~ b. } false~. math. }
  { xapps. xapps. xapps.
    { apply~ index_of_inbound. }
    xapps. xapps. xapps.
    { apply~ index_of_inbound. }
    xapps. xapps. xapps. xapps.
    asserts~: (length L2 <> 0).
    destruct L2. { false~. }
    destruct Ljunk as [|j Ljunk'].
    { xchange~ (Buf_close b gap); auto_tilde.
      rewrite~ read_middle. rewrite~ update_middle. }
    { xchange~ (Buf_close b gap (Ljunk' & z) (z :: L1)); auto_tilde.
      rewrite~ update_middle.
      replace (rev L1 ++ j :: Ljunk' ++ z :: L2) with ((rev L1 ++ j :: Ljunk') ++ z :: L2)
                                                      by rew_list~.
      rewrite~ read_middle. } }
Qed.

Lemma right_spec' : forall b L pos,
  app right [b]
    PRE (b ~> Buf' L pos)
    POST (fun (tt:unit) =>
      If pos < length L then b ~> Buf' L (pos + 1) else b ~> Buf' L pos).
Proof.
  introv. unfold hdata.
  unfold Buf'. xpull. intros L1 L2 gap (? & ?). subst L.
  destruct~ L2.
  { case_if~. { false. math. } xapply~ right_spec. }
  { case_if~; swap 1 2. { false~. } xapply~ right_spec. }
Qed.

Lemma grow_spec : forall k b L1 L2 gap,
  app grow [k b]
    PRE (b ~> Buf L1 L2 gap \* \[ k >= 0 ])
    POST (fun (tt:unit) => b ~> Buf L1 L2 (gap + k)).
Proof.
  intros. xcf.

  xpull.
  intros Hk.

  xopen b.
  xpull.
  intros l r ljunk buf ?.
  unpack.
  xapps. xapps. xapp as buf'; only 1: auto_tilde.
  intros L HL.
  xapps.
  xfor_inv (fun (i:int) =>
    Hexists L',
      buf' ~> Array L' \* \[
      forall k, 0 <= k < i -> L'[k] = (rev L1)[k] ] ).
  - math.
  - admit.
  - admit.
  - admit.
  Unshelve. exact \[].
Qed.

Lemma insert_spec : forall b x L1 L2 (gap:int),
  app insert [b x]
    PRE (b ~> Buf L1 L2 gap \* \[gap > 0])
    POST (fun (tt:unit) => b ~> Buf (x :: L1) L2 (gap - 1)).
Proof.
  intros. xcf.

  xpull.
  intros Hgap.

  xopen b.
  xpull.
  intros l r ljunk buf ?.
  unpack.
  xapps. xapps.
  xrets.
  xif.
  - xfail. math.
  - destruct ljunk; only 1: false~.
    xapps. xapps.
    xapps.
    { apply~ index_of_inbound. }
    xapps. xapps.
    xchange~ (Buf_close b (gap - 1) (ljunk));
    auto_tilde.
    rewrite~ update_middle.
Qed.

Lemma delete_spec : forall b L1 L2 gap,
  app delete [b]
    PRE (b ~> Buf L1 L2 gap)
    POST (fun (tt:unit) =>
      match L1 with
      | nil => b ~> Buf L1 L2 gap
      | x :: L1' => b ~> Buf L1' L2 (gap + 1)
      end).
Proof.
  intros. xcf.
  xopen b.
  xpull.
  intros l r ljunk buf ?.
  unpack.
  xapps. xrets.
  xif.
  - xapps. xapps.
    destruct L1; only 1: false~.
    rew_list in *.
    xchange~ (Buf_close b (gap + 1) (z :: ljunk)).
    math.
  - xrets.
    assert (L1 = nil) as -> by apply~ length_zero_inv.
    xclose~ b.
Qed.