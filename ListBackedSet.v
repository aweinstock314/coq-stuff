Require Import Setoid.

Lemma andb_idem : forall b, (b && b = b)%bool. destruct b; reflexivity. Qed.
Lemma andb_assoc : forall a b c, ((a && b) && c = a && (b && c))%bool. destruct a,b,c; reflexivity. Qed.
Lemma andb_prop' : forall a b : bool, a = true /\ b = true -> (a && b)%bool = true.
    intros a b H. destruct a, b; easy. Qed.
Lemma andb_prop_iff : forall a b : bool, (a = true /\ b = true) <-> ((a && b)%bool = true).
    destruct a,b; tauto. Qed.

Module ListBackedSet.
    (*Parameter A : Type.
    Parameter dec_eq : forall x y : A, {x = y} + {x <> y}.*)
    Fixpoint elem (A : Type) (dec_eq : forall x y : A, {x = y} + {x <> y}) x l : bool :=
        match l with nil => false | cons y ys => orb (sumbool_rec (fun _ => bool) (fun _ => true) (fun _ => false) (dec_eq x y)) (elem A dec_eq x ys) end.
    Fixpoint subset A dec_eq l1 l2 : bool :=
        match l1 with nil => true | cons y ys => andb (elem A dec_eq y l2) (subset A dec_eq ys l2) end.
    Definition eqset A dec_eq l1 l2 : bool := andb (subset A dec_eq l1 l2) (subset A dec_eq l2 l1).
    Fixpoint map {A B : Type} (f : A -> B) (l : list A) := match l with nil => nil | cons x xs => cons (f x) (map f xs) end.
    Fixpoint powerset {A} (l : list A) : list (list A) := match l with nil => (cons nil nil) | cons x xs => app (powerset xs) (map (cons x) (powerset xs)) end.

    Fixpoint expnat b e := match e with 0 => 1 | S e' => b * expnat b e' end.

    Ltac simple_nat_induction n c1 c2 := intros; induction n as [ | n IHn ]; simpl; [ c1 | rewrite IHn; c2 ]; reflexivity.
    Ltac simple_list_induction n c1 c2 := intros; induction n as [ | x xs IHxs ]; simpl; [ c1 | c2; rewrite IHxs ]; reflexivity.

    Theorem length_app_plus : forall A (xs ys : list A), length (app xs ys) = length xs + length ys. simple_list_induction xs idtac idtac. Qed.
    Theorem plus_rightid : forall n, n + 0 = n. simple_nat_induction n idtac idtac. Qed.
    Theorem plus_double : forall n, n + n = 2 * n.  intros n; induction n; simpl; [|rewrite plus_rightid]; reflexivity. Qed.
    Theorem length_map : forall (A B : Type) (f : A -> B) xs, length xs = length (map f xs). simple_list_induction xs idtac idtac. Qed.

    Theorem powerset_length : forall (A : Type) (l : list A), length (powerset l) = expnat 2 (length l).
        simple_list_induction l idtac ltac:(rewrite length_app_plus, plus_rightid, <- (@ length_map (list A) (list A) (cons x))).
    Qed.

    Definition union := app.
    Fixpoint intersection A dec_eq l1 l2 := match l1 with
        | nil => nil
        | cons x xs => (if elem A dec_eq x l2 then cons x else (fun a => a)) (intersection A dec_eq xs l2)
        end.

    Theorem subset_nil : forall A dec_eq (x : list A), subset A dec_eq x nil = true -> x = nil.
        (intros ** ). (induction x). reflexivity. (compute in H). discriminate H. Qed.
    Theorem subset_antisym : forall A dec_eq (x y : list A), subset A dec_eq x y = true /\ subset A dec_eq y x = true -> eqset A dec_eq x y = true.
        intros. (simpl). (unfold eqset). (destruct H). (rewrite H, H0). (simpl). reflexivity. Qed.
    Theorem elem_liftbool : forall A dec_eq (a b : A) (x : list A), elem A dec_eq a (b :: x)%list = true -> (a = b \/ (a <> b /\ elem A dec_eq a x = true)).
        intros A dec_eq a b x H; inversion H; destruct dec_eq as [e | n]; [ exact (or_introl e) | right; (unfold sumbool_rec, sumbool_rect); exact (conj n eq_refl)]. Qed.
    Theorem elem_cons_eq : forall A dec_eq (a b : A) (x : list A), a = b -> elem A dec_eq a (b :: x)%list = true.
        intros A dec_eq a b x e; rewrite e; compute; destruct (dec_eq b b); [|contradict n]; reflexivity. Qed.
    Theorem elem_cons_neq : forall A dec_eq (a b : A) (x : list A), a <> b -> elem A dec_eq a (b :: x)%list = elem A dec_eq a x.
        intros A dec_eq a b x n; simpl; unfold sumbool_rec, sumbool_rect; destruct dec_eq as [e|_]; [exact match n e with end | reflexivity]. Qed.
    Theorem elem_cons_extend : forall A dec_eq (a b : A) (xs : list A), elem A dec_eq a xs = true -> elem A dec_eq a (b :: xs) = true.
        intros A dec_eq a b xs a_in_xs; destruct (dec_eq a b); [exact (elem_cons_eq A _ a b xs e) | rewrite (elem_cons_neq A _ a b xs n); exact a_in_xs]. Qed.
    (*Theorem subset_lcons : forall A dec_eq (a : A) (x y : list A), subset A dec_eq (a :: x) y = true -> subset A dec_eq x y = true.
(intros A dec_eq a x y H). (induction x).
    - reflexivity.
    -*)
    (*Theorem subset_rcons : forall A dec_eq (a : A) (x y : list A), subset A dec_eq x (a :: y) = true -> elem A dec_eq a x = true \/ subset A dec_eq x y = true.
        intros A dec_eq a x y H. induction x.
        - simpl. tauto.
        - simpl. unfold sumbool_rec. unfold sumbool_rect. destruct dec_eq.
            + simpl. tauto.
            + simpl.*)
    (*Theorem subset_constail : forall A dec_eq (a : A) (x y : list A), subset A dec_eq x y = true -> subset A dec_eq x (a :: y) = true.
        intros A dec_eq a x y H.*)
    (*Theorem subset_refl : forall A dec_eq (x : list A), subset A dec_eq x x = true.
    intros A dec_eq x. induction x .
    - reflexivity.
    - simpl. unfold sumbool_rec. unfold sumbool_rect. destruct dec_eq.
        + simpl.
    *)
    (*Theorem subset_trans : forall A dec_eq (x y z : list A), subset A dec_eq x y = true /\ subset A dec_eq y z = true -> subset A dec_eq x z = true.
        (intros ** ).  (destruct H).  (induction y).
        - (rewrite (subset_nil A dec_eq x H)).  (apply H0).
        - 
    *)

    Theorem subset_prop_cons : forall A eq_dec (ys xs : list A) (x : A), subset A eq_dec (x :: xs) ys = true -> elem A eq_dec x ys = true /\ subset A eq_dec xs ys = true.
        intros A eq_dec ys. induction ys; intros xs x H.
        - discriminate H.
        - unfold subset in H. apply andb_prop in H. fold subset in H. exact H.
        Qed.

End ListBackedSet.

Module ListBackedSet'.
    Inductive Elem {A} (x : A) : (list A) -> Prop := Elem_head : forall xs, Elem x (cons x xs) | Elem_tail : forall y xs, Elem x xs -> Elem x (cons y xs).
    Definition Subset {A} (xs ys : list A) := forall x, Elem x xs -> Elem x ys.
    Definition EqSet {A} (xs ys : list A) := Subset xs ys /\ Subset ys xs.

    Theorem elem_compat : forall A eq_dec x xs, ListBackedSet.elem A eq_dec x xs = true <-> Elem x xs.
        intros A eq_dec x xs. induction xs; [easy | split].
        - destruct (eq_dec x a).
            + intro H. rewrite e. apply Elem_head.
            + rewrite (ListBackedSet.elem_cons_neq _ _ _ _ _ n).
                intro H. exact (Elem_tail _ _ _ (proj1 IHxs H)).
        - intro H. inversion H.
           + apply ListBackedSet.elem_cons_eq; reflexivity.
           + subst. exact (ListBackedSet.elem_cons_extend _ _ _ _ _ (proj2 IHxs H1)).
        Qed.

    Theorem Subset_lcontract {A} : forall x (xs ys : list A), Subset (x :: xs) ys -> Subset xs ys.
        intros x xs ys H y H'. exact (H _ (Elem_tail _ _ _ H')). Qed.
    Theorem Subset_rexpand {A} : forall y (xs ys : list A), Subset xs ys -> Subset xs (y :: ys).
        intros y xs ys H x H'. exact (Elem_tail _ _ _ (H x H')). Qed.

    Theorem subset_compat : forall A eq_dec xs ys, ListBackedSet.subset A eq_dec xs ys = true <-> Subset xs ys.
        intros A eq_dec xs ys. split.
        - induction xs.
            + simpl. unfold Subset. intros H x H'. inversion H'.
            + intros. unfold Subset. intros x H'.
                apply andb_prop in H. fold ListBackedSet.subset in H. destruct H as [He Hs].
                specialize (IHxs Hs x). apply elem_compat in He. destruct (eq_dec a x).
                * subst; exact He.
                * inversion H'; subst;  tauto.
        - induction xs.
            + reflexivity.
            + intro H. apply andb_prop'. fold ListBackedSet.subset. split.
                * exact (proj2 (elem_compat _ _ _ _) (H a (Elem_head _ _))).
                * exact (IHxs (Subset_lcontract _ _ _ H)).
        Qed.

    Theorem eqset_compat : forall A eq_dec xs ys, ListBackedSet.eqset A eq_dec xs ys = true <-> EqSet xs ys.
        intros A eq_dec xs ys. unfold ListBackedSet.eqset. rewrite <- andb_prop_iff. repeat rewrite subset_compat. reflexivity.
        Qed.
End ListBackedSet'.
