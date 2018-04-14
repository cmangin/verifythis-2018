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
Ltac auto_tilde ::= (* try unfold LibListZ.length in *;  *)rew_list in *; eauto with maths.

Inductive color := R | B.
Definition coloring := list color.

(* Z_lt_le_dec: forall x y : int, {x < y} + {y <= x} *)

Fixpoint coloring_valid (aux: int) (c : coloring) : bool :=
  match c with
  | B :: cs => if Z_lt_le_dec aux 3 then false else coloring_valid 0 cs
  | R :: cs => coloring_valid (aux + 1) cs
  | nil => if Z_lt_le_dec aux 3 then false else true
  end.

Definition invariant (n: int) (counts: list int) (colorings: list (list coloring)) :=
  length counts = n /\
  length colorings = n /\
  forall i, 0 <= i < n ->
    counts[i] = length colorings[i] /\
    Forall (fun c => length c = i) colorings[i].

Lemma docount_spec : forall (a: array int) (L: list int),
  length L >= 4 ->
  app docount [a]
    PRE (a ~> Array L)
    POST (fun (tt:unit) =>
            Hexists L' C,
            a ~> Array L' \* \[ invariant (length L') L' C ]).
Proof.
  introv. xcf.
  xapps. xapps. { apply~ index_of_inbound.  }
  xapps. { apply~ index_of_inbound. rewrite length_update. math. }
  xapps. { apply~ index_of_inbound. rewrite !length_update. math. }
  xapps. { apply~ index_of_inbound. rewrite !length_update. math. }
  xfor_inv (fun n => Hexists L0 Ljunk C,
                     a ~> Array (L0 ++ Ljunk) \*
                     \[ length L0 = n /\
                        length L0 + length Ljunk = length L /\
                        invariant n L0 C ]).
  { math. }
  { do 4 (destruct L as [|? L];  try solve [ false~ ]).
    hsimpl (>> (1 :: 1 :: 1 :: 2 :: nil) L
               ((nil :: nil) :: ((B :: nil) :: nil) :: ((B :: B :: nil) :: nil) ::
                             ((B::B::B::nil) :: (R::R::R::nil) :: nil) :: nil)).
    rew_list. rewrite update_zero. rewrite~ update_cons_pos.
    rewrite update_zero. repeat (try rewrite update_zero; rewrite~ update_cons_pos).
    repeat f_equal. rewrite update_zero. f_equal.
    splits~. unfolds~ invariant. splits~.
    { intros i Hi.
      admit. } }
  { intros n (Hilo & Hihi).
    xpull. intros L0 Ljunk C (? & (I1 & I2)).
    xapps. { apply~ index_of_inbound. }
    xapps. { apply~ index_of_inbound. }
    destruct Ljunk as [| ? Ljunk']. { false~. math. }
    rewrite update_middle with (l1 := L0) (l2 := Ljunk'); [| auto_tilde].
    rew_list in I1.
    pose (C' := map (cons B) C[n-1]).
    assert ((L0 ++ z :: Ljunk')[n-1] = L0[n-1]) as ->.
    { rewrite read_app. case_if~. }
    xfor_inv (fun (k:int) =>
      Hexists (count: int) (C': list coloring),
        a ~> Array (L0 ++ count :: Ljunk') \*
        \[ count = length C' /\
           Forall (fun c => length c = n) C'
        ]).
    { math. }
    { hsimpl L0[n-1] C'.
      { rew_list. reflexivity. }
      { splits~.
        - unfold invariant in I2. unpack.
          subst C'. rewrite length_map. apply~ H3.
        - unfold invariant in I2. unpack.
          subst C'.
          forwards~: H3 (n-1). unpack.

          Lemma Forall_map {A B : Type} { P : B -> Prop} {f : A -> B} {l: list A} :
            Forall (fun x => P (f x)) l ->
            Forall P (map f l).
          Proof. induction 1; now constructor. Qed.
          apply Forall_map.

          apply (Forall_pred_incl H5). unfold pred_incl.
          intros. auto_tilde. } }
    { intros k (Hk1 & Hk2). xpull. intros count C'0 (II1 & II2).
      xapps. { apply~ index_of_inbound. }
      xapps. { apply~ index_of_inbound. }
      xapps. { apply~ index_of_inbound. }
      hsimpl
        (count + L0[n-k-1])
        ((map (fun c => ((make k R) ++ B :: c)) C[n-k-1]) ++ C'0).
      { rewrite read_middle with (x := count); [|auto_tilde].
        rewrite update_middle with (w := count); [| auto_tilde].
        assert ((L0 ++ count :: Ljunk')[(n-k)-1] = L0[n-k-1]) as ->. {
          rewrite read_app. case_if~. }
        rew_list~. }
      { splits~.
        { rewrite length_map. unfold invariant in I2. unpack.
          rewrite II1. forwards~: H3 ((n-k)-1). unpack.
          rewrite H4. rewrite Z.add_comm. reflexivity. }
        { admit. } } }
    { admit. } }
  { admit. }
Qed.
