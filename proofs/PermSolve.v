Require Import List Arith Omega.
Import ListNotations.

Require Import Permutation Sorting.

Module Type WithType.
  Variable A : Type.
End WithType.

Module PairOrder (T : WithType) <: Orders.TotalLeBool.
  Definition t := (nat * T.A)%type.
  Definition leb (x y : t) := Nat.leb (fst x) (fst y).
  Lemma leb_total : forall a b, is_true (leb a b) \/ is_true (leb b a).
  Proof.
    intros.
    destruct a, b; unfold leb; simpl.
    destruct (n <=? n0) eqn:?; [now left | right].
    destruct (n0 <=? n) eqn:?; auto.
    apply Nat.leb_gt in Heqb.
    apply Nat.leb_gt in Heqb0.
    omega.
  Qed.
End PairOrder.

Module PermutationSolve (T : WithType).
  Include T.

  Inductive rlist : Type :=
  | Nil : rlist
  | Var : nat -> list A -> rlist
  | Cons : nat -> A -> rlist -> rlist
  | App : rlist -> rlist -> rlist.

  Fixpoint rlistDenote (r : rlist) : list A :=
  match r with
  | Nil => []
  | Var _ l => l
  | Cons _ x r => x :: rlistDenote r
  | App r1 r2 => rlistDenote r1 ++ rlistDenote r2
  end.

  Fixpoint normalize_aux (r : rlist) : list (nat * A) * list (nat * list A) :=
  match r with
  | Nil => ([], [])
  | Var i l => ([], [(i, l)])
  | Cons i x r => let (a, b) := normalize_aux r in ((i, x) :: a, b)
  | App r1 r2 => let (a1, b1) := normalize_aux r1 in
                 let (a2, b2) := normalize_aux r2 in
                   (a1 ++ a2, b1 ++ b2)
  end.

  Module PO := PairOrder T.
  Module AS := Sort PO.

  Module TL <: WithType.
    Definition A := list A.
  End TL.

  Module POL := PairOrder TL.
  Module ASL := Sort POL.

  Definition normalize (r : rlist) : list A :=
    let (a, b) := normalize_aux r in
    let a := AS.sort a in
    let a := map snd a in
    let b := ASL.sort b in
    let b := map snd b in
    let b := concat b in
      a ++ b.

  Ltac remove_fun f t :=
    match t with
    | context C[f ?l] =>
      let t := context C[l] in remove_fun f t
    | _ => t
    end.

  Ltac remove_funs fs t :=
    match fs with
    | True => t
    | (?f, ?fs) =>
      let t := remove_fun f t in
        remove_funs fs t
    end.

  Ltac trans_funs fs :=
    match goal with
    |- Permutation ?l1 ?l2 =>
        let l1' := remove_funs fs l1 in
        let l2' := remove_funs fs l2 in
          apply perm_trans with l1';[|apply perm_trans with l2']
    end.

  Lemma Permutation_concat {A : Type} (l1 l2 : list (list A)) :
    Permutation l1 l2 -> Permutation (concat l1) (concat l2).
  Proof.
    induction 1; simpl in *.
    - constructor.
    - now apply Permutation_app_head.
    - rewrite !app_assoc. apply Permutation_app_tail.
      apply Permutation_app_comm.
    - eapply perm_trans; eassumption.
  Qed.

  Ltac trans_sorts :=
     let finish :=
       repeat (apply perm_skip || apply Permutation_app ||
               apply Permutation_map || apply Permutation_concat ||
               apply AS.Permuted_sort || apply ASL.Permuted_sort ||
               (apply Permutation_sym;
               (apply AS.Permuted_sort || apply ASL.Permuted_sort))) in
     trans_funs constr:((AS.sort, (ASL.sort, True)));
     [finish| | finish].

  Theorem normalize_correct : forall (r : rlist),
    Permutation (rlistDenote r) (normalize r).
  Proof.
    induction r; unfold normalize in *; simpl in *.
    - constructor.
    - rewrite app_nil_r. apply Permutation_refl.
    - destruct (normalize_aux r).
      apply perm_trans with (a :: map snd (AS.sort l) ++ concat (map snd (ASL.sort l0)));
      [now apply perm_skip|clear].
      trans_sorts.
      apply Permutation_refl.
    - destruct (normalize_aux r1). destruct (normalize_aux r2).
      apply perm_trans with ((map snd (AS.sort l) ++ concat (map snd (ASL.sort l0))) ++
        (map snd (AS.sort l1) ++ concat (map snd (ASL.sort l2))));
      [now apply Permutation_app|clear].
      trans_sorts.
      rewrite !map_app, !concat_app, !app_assoc_reverse.
      apply Permutation_app_head.
      rewrite !app_assoc. apply Permutation_app_tail.
      apply Permutation_app_comm.
  Qed.

  Ltac get_idx_aux l x k :=
  match l with
  | True => constr:(((x, True), k))
  | (x, _) => constr:((l, k))
  | (?h, ?l) =>
      match get_idx_aux l x constr:(S k) with
      | (?l, ?k) => constr:(((h, l), k))
      end
  end.
  Ltac get_idx l x := get_idx_aux l x O.

  Ltac reify l vars :=
    match l with
    | [] => constr:((vars, Nil))
    | ?x :: ?l =>
        match reify l vars with
        | (?vars, ?r) =>
        match get_idx vars x with
        | (?vars, ?i) => constr:((vars, (Cons i x r)))
        end end
    | ?l1 ++ ?l2 =>
        match reify l1 vars with
        | (?vars, ?r1) =>
        match reify l2 vars with
        | (?vars, ?r2) =>
          constr:((vars, App r1 r2))
        end end
    | ?l =>
        match get_idx vars l with
        | (?vars, ?i) => constr:((vars, Var i l))
        end
    end.

  Ltac reify_goal :=
    match goal with
    |- Permutation ?l1 ?l2 =>
        let vars := constr:(True) in
        match reify l1 vars with
        | (?vars, ?r1) =>
        match reify l2 vars with
        | (?vars, ?r2) =>
          let vr1 := fresh "r1" in
          let vr2 := fresh "r2" in
          set (vr1 := r1); set (vr2 := r2);
          change (Permutation (rlistDenote vr1) (rlistDenote vr2))
        end end
    end.

  Ltac solve_perm := reify_goal;
    match goal with
    | |- Permutation (rlistDenote ?r1) (rlistDenote ?r2) =>
        apply perm_trans with (normalize r1); [apply normalize_correct|
        apply perm_trans with (normalize r2); [apply Permutation_refl|
        apply Permutation_sym; apply normalize_correct]]
    end.
End PermutationSolve.
