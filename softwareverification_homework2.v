Require Omega.

Module Part1.
    (* Coq's standard library's ordering on peano nats defines <= as given by the rules (forall n, n <= n) and (forall n m, n <= m -> n <= S m) (i.e. reflexivity and right-successor).
        (x < y) is an alias for (S x <= y), and (y < x) is an alias for (x < y). *)

    (* nat_compare is a decideable trichotomy for peano naturals (i.e. given two nats, it computes which ordering holds between them) *)
    Definition or_inj1 {P Q R : Prop} : P -> {P} + {Q} + {R} := ltac:(tauto).
    Definition or_inj2 {P Q R : Prop} : Q -> {P} + {Q} + {R} := ltac:(tauto).
    Definition or_inj3 {P Q R : Prop} : R -> {P} + {Q} + {R} := ltac:(tauto).
    Fixpoint nat_compare (n m : nat) : {n < m} + {n = m} + {n > m} :=
        match n with
        | 0 => match m with
            | 0 => or_inj2 eq_refl
            | S m' => or_inj1 (le_n_S _ _ (le_0_n m'))
            end
        | S n' => match m with
            | 0 => or_inj3 (le_n_S _ _ (le_0_n n'))
            | S m' => match nat_compare n' m' with
                | inleft (left less) => inleft (left (le_n_S _ _ less))
                | inleft (right equal) => inleft (right (f_equal S equal))
                | inright greater => inright (le_n_S _ _ greater)
                end
            end
        end.

    (* trichotomy is an Ltac script that flattens the structure of the result of nat-compare, to be used in proofs/definitions by cases *)
    Ltac trichotomy x y := destruct (nat_compare x y) as [s | ?g]; [destruct s as [?l | ?e]|].

    Definition max' : nat -> nat -> nat.
        intros n m. trichotomy n m.
        - (* n < m *) exact m.
        - (* n = m *) exact n.
        - (* n > m *) exact n.
        Defined.
        
    (* Idempotence is easy to prove; running the comparison on x and x yields a goal of showing x = x, which is discharged by reflexivity in all 3 cases. *)
    Theorem max'_idempotent : forall x, max' x x = x.
        intro x; unfold max'; trichotomy x x; reflexivity.
        Qed.

    (* Some helper lemmas on inequalities *)
    Lemma lt_irreflexive : forall x, ~(x < x).
        intros x e. unfold lt in e. induction x; inversion e.
        - rewrite H0 in e. exact (IHx e).
        - subst. exact (IHx (le_pred _ _ (le_S _ _ H0))).
        Qed.

    Lemma not_le_plus_l : forall n k, ~((S k) + n <= n).
        induction k; intro e.
        - exact (lt_irreflexive _ e).
        - exact (IHk (le_pred _ _ (le_S _ _ e))).
        Qed.

    Lemma le_trans : forall x y z, x <= y -> y <= z -> x <= z.
        induction x, y, z; try easy; intros Hxy Hyz.
        - apply le_0_n.
        - exact (le_n_S _ _ (IHx y z (le_pred _ _ Hxy) (le_pred _ _ Hyz))).
        Qed.

    (* fully-automatic versions of the above lemmas, with the omega tactic (a Presburger arithmetic solver) *)
    Module Omega_demo.
        Import Omega.
        Lemma lt_irreflexive' : forall x, ~(x < x). intros; omega. Qed.
        Lemma not_le_plus_l' : forall n k, ~((S k) + n <= n). intros; omega. Qed.
        Lemma le_trans' : forall x y z, x <= y -> y <= z -> x <= z. intros; omega. Qed.
    End Omega_demo.
    

    (* reduction lemmas for max, max'_0_l and max'_S are the ones that ended up being used, the ones with disjunctions in their RHS ended up being too cumbersome to use *)
    Lemma max'_0_l : forall x, max' 0 x = x.
        destruct x.
        - reflexivity.
        - unfold max'. trichotomy 0 (S x).
          + reflexivity.
          + exact e.
          + inversion g.
        Qed.

    Lemma max'_S_l : forall x y, max' (S x) y = S (max' x y) \/ max' (S x) y = y.
        intros x y. unfold max'. trichotomy (S x) y.
        - right. reflexivity.
        - right. exact e.
        - left. trichotomy x y; try easy. destruct (lt_irreflexive _ (le_trans _ _ _ g l)).
        Qed.
    Lemma max'_S_l' : forall x y, max' (S x) y = S x \/ max' (S x) y = y.
        intros x y. unfold max'. trichotomy (S x) y.
        - right. reflexivity.
        - right. exact e.
        - left. reflexivity.
        Qed.

    Ltac double_inversion H := inversion H as [| ? ?H' ]; inversion H'.
    Ltac recursive_inversion H := inversion H as [| ? ?H' ]; try recursive_inversion H'.

    Lemma max'_S : forall x y, max' (S x) (S y) = S (max' x y).
        induction x; intro y.
        - rewrite max'_0_l. unfold max'.
            trichotomy 1 (S y); try easy. recursive_inversion g.
        - unfold max'. trichotomy (S x) y; trichotomy (S (S x)) (S y); try easy.
            + set (H := le_trans _ _ _ g l). destruct (not_le_plus_l y 1 H).
            + subst. reflexivity.
            + set (H := le_trans _ _ _ l g). destruct (not_le_plus_l (S x) 1 H).
        Qed.

    (* max_compat_max' shows that max' defined via trichotomy has the same behavior as a version defined directly via recursion on peano naturals; the latter is more transparent to Coq's reduction machinery.
        This makes use of the reduction lemmas defined above. *)
    
    Lemma max_compat_max' : forall n m, max' n m = Nat.max n m.
        induction n; intro m.
        - apply max'_0_l.
        - induction m.
            + trichotomy (S n) 0; easy.
            + simpl. rewrite <- (IHn m). rewrite max'_S. reflexivity.
        Qed.

    (* once max_compat_max' has been proven, max'_associative is proven by routine induction on peano naturals (with some care taken to ensure that the generated inductive hypothesis is general enough *)
    Theorem max'_associative : forall x y z, max' x (max' y z) = max' (max' x y) z.
        intros x y z.
        repeat rewrite max_compat_max'.
        revert z; revert y; induction x; destruct y, z; try reflexivity.
        simpl. rewrite (IHx y z).
        reflexivity.
        Qed.
End Part1.

Load ListBackedSet.
Import ListBackedSet.
Import ListBackedSet'.

Module Part2.
    Definition relation (S T : Type) := list (S * T).

    Definition domain {S T} (rel : relation S T) := map fst rel.
    Definition range {S T} (rel : relation S T) := map snd rel.

    Lemma range_theorem_2_lemma_1 {S T} : forall (r1 r2 : relation S T) xs ys (x : S * T), Intersection r1 r2 xs -> Intersection (range r1) (range r2) ys -> Elem x xs -> Elem (snd x) ys.
        intros r1 r2 xs ys x Int_xs Int_ys x_in_xs.
        unfold Intersection in *.
        destruct (proj1 (Int_xs x) x_in_xs) as [xr1 xr2].
        apply (map_elem snd) in xr1; apply (map_elem snd) in xr2.
        fold (range r1) in xr1; fold (range r2) in xr2.
        exact (proj2 (Int_ys (snd x)) (conj xr1 xr2)).
        Qed.

    Theorem range_theorem_2 {S T} : forall (r1 r2 : relation S T) xs ys, Intersection r1 r2 xs -> Intersection (range r1) (range r2) ys -> Subset (range xs) ys.
        intros r1 r2 xs ys Int_xs Int_ys x x_in_xs.
        destruct (co_map_elem_inhabited snd _ _ x_in_xs) as [st [ist est]].
        set (H := range_theorem_2_lemma_1 r1 r2 _ _ st Int_xs Int_ys ist).
        rewrite est in H. exact H.
        Qed.

End Part2.
