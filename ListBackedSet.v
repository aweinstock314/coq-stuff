Require Import Setoid.

Lemma andb_idem : forall b, (b && b = b)%bool. destruct b; reflexivity. Qed.
Lemma andb_assoc : forall a b c, ((a && b) && c = a && (b && c))%bool. destruct a,b,c; reflexivity. Qed.
Lemma andb_prop' : forall a b : bool, a = true /\ b = true -> (a && b)%bool = true.
    intros a b H. destruct a, b; easy. Qed.
Lemma andb_prop_iff : forall a b : bool, (a = true /\ b = true) <-> ((a && b)%bool = true).
    destruct a,b; tauto. Qed.

Definition DecEq A := forall x y : A, {x = y} + {x <> y}.
Definition DecEqPair {S T} : DecEq S -> DecEq T -> DecEq (S * T).
    intros eS eT [s1 t1] [s2 t2].
    destruct (eS s1 s2), (eT t1 t2); subst;
        try (left; reflexivity); 
        (right; intro H; inversion H; easy).
    Defined.

Definition Injective {A B} (f : A -> B) := forall x x', f x = f x' -> x = x'.
Definition Surjective {A B} (f : A -> B) := forall y, {x | f x = y}.
Definition LeftInvertible {A B} (f : A -> B) := exists g, forall x, g (f x) = x.
Definition Invertible {A B} (f : A -> B) := {g | forall x y, f x = y <-> g y = x}.

Example not_left_implies_right_invertable : ~(forall A B (f : A -> B) (g : B -> A), (forall x, g (f x) = x) -> (forall y, f (g y) = y)).
    intros H.
    discriminate (H True bool (fun _ => false) (fun _ => I) (fun x => match x with I => eq_refl end) true).
    Qed.

Definition iffT P Q := prod (P -> Q) (Q -> P).

Lemma invertable_alternate_characterization {A B}: forall (f : A -> B), iffT (Invertible f) (prod (Injective f) (Surjective f)).
    unfold Invertible, Injective, Surjective. intro f. split.
    (* Invertible -> Injective /\ Surjective *)
    - intros [g g_inv_f]. split.
        (* Invertible -> Injective *)
        + intros x x' eq_f. apply (f_equal g) in eq_f. repeat rewrite (proj1 (g_inv_f _ _) eq_refl) in eq_f. exact eq_f.
        (* Invertible -> Surjective *)
        + intros y. exists (g y). exact (proj2 (g_inv_f _ y) eq_refl).
    (* Injective /\ Surjective -> Invertible *)
    - intros [inj surj]. exists (fun y => proj1_sig (surj y)). intros x y. split; intro e.
        (* f x = y -> g y = x *)
        + destruct (surj y) as [x' e']. simpl. rewrite <- e in e'. exact (inj _ _ e').
        (* g y = x -> f x = y *)
        + destruct (surj y) as [x' e']. simpl in e. rewrite e in e'. exact e'.
    Qed.

Module ListBackedSet.
    (*Parameter A : Type.
    Parameter eq_dec : forall x y : A, {x = y} + {x <> y}.*)
    Fixpoint elem (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) x l : bool :=
        match l with nil => false | cons y ys => orb (sumbool_rec (fun _ => bool) (fun _ => true) (fun _ => false) (eq_dec x y)) (elem A eq_dec x ys) end.
    Fixpoint subset A eq_dec l1 l2 : bool :=
        match l1 with nil => true | cons y ys => andb (elem A eq_dec y l2) (subset A eq_dec ys l2) end.
    Definition eqset A eq_dec l1 l2 : bool := andb (subset A eq_dec l1 l2) (subset A eq_dec l2 l1).
    Fixpoint map {A B : Type} (f : A -> B) (l : list A) := match l with nil => nil | cons x xs => cons (f x) (map f xs) end.

    Lemma map_cons {A B} : forall (f : A -> B) x xs, (map f (x :: xs) = f x :: map f xs)%list.
        destruct xs; reflexivity. Qed.
    Lemma map_compose {A B C} (f : A -> B) (g : B -> C) : forall xs, map g (map f xs) = map (fun x => g (f x)) xs.
        induction xs; simpl; [| rewrite IHxs]; reflexivity. Qed.
    Lemma map_f_equal {A B} (f : A -> B) (g : B -> A) : forall xs, (forall x, g (f x) = x) -> xs = map (fun x => g (f x)) xs.
        induction xs; intro e; simpl; [|repeat rewrite <- (IHxs e); rewrite e]; reflexivity. Qed.

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
    Fixpoint intersection {A} eq_dec l1 l2 := match l1 with
        | nil => nil
        | cons x xs => (if elem A eq_dec x l2 then cons x else (fun a => a)) (@ intersection A eq_dec xs l2)
        end.

    (*Infix "/-\" := intersection : LBS_scope.
    Infix "\-/" := union : LBS_scope.*)

    Theorem subset_nil : forall A eq_dec (x : list A), subset A eq_dec x nil = true -> x = nil.
        (intros ** ). (induction x). reflexivity. (compute in H). discriminate H. Qed.
    Theorem subset_antisym : forall A eq_dec (x y : list A), subset A eq_dec x y = true /\ subset A eq_dec y x = true -> eqset A eq_dec x y = true.
        intros. (simpl). (unfold eqset). (destruct H). (rewrite H, H0). (simpl). reflexivity. Qed.
    Theorem elem_liftbool : forall A eq_dec (a b : A) (x : list A), elem A eq_dec a (b :: x)%list = true -> (a = b \/ (a <> b /\ elem A eq_dec a x = true)).
        intros A eq_dec a b x H; inversion H; destruct eq_dec as [e | n]; [ exact (or_introl e) | right; (unfold sumbool_rec, sumbool_rect); exact (conj n eq_refl)]. Qed.
    Theorem elem_cons_eq : forall A eq_dec (a b : A) (x : list A), a = b -> elem A eq_dec a (b :: x)%list = true.
        intros A eq_dec a b x e; rewrite e; compute; destruct (eq_dec b b); [|contradict n]; reflexivity. Qed.
    Theorem elem_cons_neq : forall A eq_dec (a b : A) (x : list A), a <> b -> elem A eq_dec a (b :: x)%list = elem A eq_dec a x.
        intros A eq_dec a b x n; simpl; unfold sumbool_rec, sumbool_rect; destruct eq_dec as [e|_]; [exact match n e with end | reflexivity]. Qed.
    Theorem elem_cons_extend : forall A eq_dec (a b : A) (xs : list A), elem A eq_dec a xs = true -> elem A eq_dec a (b :: xs) = true.
        intros A eq_dec a b xs a_in_xs; destruct (eq_dec a b); [exact (elem_cons_eq A _ a b xs e) | rewrite (elem_cons_neq A _ a b xs n); exact a_in_xs]. Qed.
    (*Theorem subset_lcons : forall A eq_dec (a : A) (x y : list A), subset A eq_dec (a :: x) y = true -> subset A eq_dec x y = true.
(intros A eq_dec a x y H). (induction x).
    - reflexivity.
    -*)
    (*Theorem subset_rcons : forall A eq_dec (a : A) (x y : list A), subset A eq_dec x (a :: y) = true -> elem A eq_dec a x = true \/ subset A eq_dec x y = true.
        intros A eq_dec a x y H. induction x.
        - simpl. tauto.
        - simpl. unfold sumbool_rec. unfold sumbool_rect. destruct eq_dec.
            + simpl. tauto.
            + simpl.*)
    (*Theorem subset_constail : forall A eq_dec (a : A) (x y : list A), subset A eq_dec x y = true -> subset A eq_dec x (a :: y) = true.
        intros A eq_dec a x y H.*)
    (*Theorem subset_refl : forall A eq_dec (x : list A), subset A eq_dec x x = true.
    intros A eq_dec x. induction x .
    - reflexivity.
    - simpl. unfold sumbool_rec. unfold sumbool_rect. destruct eq_dec.
        + simpl.
    *)
    (*Theorem subset_trans : forall A eq_dec (x y z : list A), subset A eq_dec x y = true /\ subset A eq_dec y z = true -> subset A eq_dec x z = true.
        (intros ** ).  (destruct H).  (induction y).
        - (rewrite (subset_nil A eq_dec x H)).  (apply H0).
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

    Definition Union {A} (xs ys zs : list A) := forall z, Elem z zs <-> Elem z xs \/ Elem z ys.
    Definition Intersection {A} (xs ys zs : list A) := forall z, Elem z zs <-> Elem z xs /\ Elem z ys.

    Definition Union' {A} (xs ys : list A) : {zs | Union xs ys zs}.
        Admitted.
    Definition Intersection' {A} (xs ys : list A) : {zs | Intersection xs ys zs}.
        Admitted.

    Lemma map_elem {A B} (f : A -> B) : forall x xs, Elem x xs -> Elem (f x) (ListBackedSet.map f xs).
        intros x xs e. induction xs; inversion e; subst.
            - rewrite ListBackedSet.map_cons. apply Elem_head.
            - apply Elem_tail. exact (IHxs H0).
        Qed.
    Lemma map_elem' {A B} (f : A -> B) (g : LeftInvertible f) : forall x xs, Elem (f x) (ListBackedSet.map f xs) -> Elem x xs.
        (* TODO: does this work with something weaker than invertable functions (e.g. surjective)? *)
        intros x xs e.
        destruct g as [g Hg].
        set (e' := map_elem g (f x) (ListBackedSet.map f xs) e).
        rewrite (ListBackedSet.map_compose f g) in e'.
        rewrite <- (ListBackedSet.map_f_equal f g _ Hg) in e'.
        rewrite Hg in e'.
        exact e'.
        Qed.

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

    Lemma elem_dec : forall A (eq_dec : DecEq A) x (xs : list A), {Elem x xs} + {~Elem x xs}.
        intros A eq_dec x xs.
        destruct (ListBackedSet.elem A eq_dec x xs) eqn:H.
        - rewrite elem_compat in H. left. exact H.
        - right. intro H'. rewrite <- elem_compat in H'. rewrite H in H'. discriminate H'.
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
            + intro H. apply andb_true_intro. fold ListBackedSet.subset. split.
                * exact (proj2 (elem_compat _ _ _ _) (H a (Elem_head _ _))).
                * exact (IHxs (Subset_lcontract _ _ _ H)).
        Qed.

    Theorem eqset_compat : forall A eq_dec xs ys, ListBackedSet.eqset A eq_dec xs ys = true <-> EqSet xs ys.
        intros A eq_dec xs ys. unfold ListBackedSet.eqset. rewrite <- andb_prop_iff. repeat rewrite subset_compat. reflexivity.
        Qed.

End ListBackedSet'.
