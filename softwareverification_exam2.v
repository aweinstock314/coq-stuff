(* (echo 'Set Ltac Debug. Load "softwareverification_exam2.v".' && (yes 's' | head -n 804)) | coqtop > softwareverification_exam2_transcript.txt *)
Module Part1.
(* Set', ++', and in' are used because the identifiers/notations/keywords Set, ++, and in are already taken *)

Inductive Set' (S : Type) := null : Set' S | insert : S -> Set' S -> Set' S.
Arguments null [S]. Arguments insert [S] h t. (* declare the type argument for the constructors of Set' implicit *)

Infix "++'" := insert (at level 50).

Definition in_def {S} := {in' : S -> Set' S -> Prop |
    (forall x, ~ in' x null) /\
    (forall x h t, in' x (h ++' t) <-> x = h \/ in' x t) }.

Definition in_def' {S} (in' : S -> Set' S -> Prop) :=
    (forall x, ~ in' x null) /\
    (forall x h t, in' x (h ++' t) <-> x = h \/ in' x t).

Definition diff_def {S} (in_spec : in_def) := 
    let in' := proj1_sig in_spec in {diff : Set' S -> Set' S -> Set' S |
    (forall x, diff null x = null) /\
    (forall h t A, in' h A -> diff (h ++' t) A = diff t A) /\
    (forall h t A, ~in' h A -> diff (h ++' t) A = h ++' diff t A) }.

Definition diff_def' {S} in' (in_spec : in_def' in') (diff : Set' S -> Set' S -> Set' S) := 
    (forall x, diff null x = null) /\
    (forall h t A, in' h A -> diff (h ++' t) A = diff t A) /\
    (forall h t A, ~in' h A -> diff (h ++' t) A = h ++' diff t A).

Theorem diff_characterization_1 :
    forall S (in_spec : in_def) (diff_spec : diff_def in_spec),
    let in' := proj1_sig in_spec in let diff := proj1_sig diff_spec in
    forall A B (x : S), in' x (proj1_sig diff_spec A B) -> in' x A /\ ~ in' x B.
Proof.
    intros S in_spec diff_spec in' diff A B x H.
    destruct in_spec as [in'' [in_prop1 in_prop2]], diff_spec as [diff' [diff_prop1 [diff_prop2 diff_prop3]]].
    unfold in', diff in *. simpl in *.
    split.
    - induction A.
        + rewrite diff_prop1 in H. exact H.
        (*+ rewrite diff_prop2 in H. specialize (IHA H). exact (proj2 (in_prop2 _ _ _) (or_intror IHA)).*)
        +
    Abort.

Definition Eq S := forall (x y : S), {x = y} + {~x=y}.

Fixpoint in' {S} (eq_dec : Eq S) (x : S) (A : Set' S) := match A with
    | null => False
    | insert y B => match eq_dec x y with
        | left _ => True
        | right _ => in' eq_dec x B
        end
    end.

Lemma in_meets_spec {S} (eq_dec : Eq S) : @ in_def' S (in' eq_dec).
Proof.
    split; simpl.
    - tauto.
    - intros x h t. destruct (eq_dec x h); tauto.
Qed.

Lemma in_dec {S} (eq_dec : Eq S) in'' (in_spec : @ in_def' S in'') x A : {in'' x A} + {~in'' x A}.
Proof.
    destruct in_spec as [in_prop1 in_prop2]. simpl.
    induction A.
    - right. apply in_prop1.
    - destruct IHA.
        + left. exact (proj2 (in_prop2 _ _ _) (or_intror i)).
        + destruct (eq_dec x s).
            * left. exact (proj2 (in_prop2 _ _ _) (or_introl e)).
            * right; intro H; destruct (proj1 (in_prop2 _ _ _) H); tauto.
Qed.

Fixpoint diff {S} (eq_dec : Eq S) (A B : Set' S) := match A with
    | null => null
    | h ++' t => match in_dec eq_dec (in' eq_dec) (in_meets_spec eq_dec) h B with
        | left _ => diff eq_dec t B
        | right _ => h ++' diff eq_dec t B
        end
    end.

Lemma diff_meets_spec {S} (eq_dec : Eq S) : @ diff_def' S (in' eq_dec) (in_meets_spec eq_dec) (diff eq_dec).
Proof.
    split.
    - tauto.
    - split; intros h t A; simpl; destruct in_dec; tauto.
Qed.

Theorem diff_characterization_1 :
    forall S (eq_dec : Eq S), forall A B (x : S), in' eq_dec x (diff eq_dec A B) -> in' eq_dec x A /\ ~ in' eq_dec x B.
Proof.
    intros S eq_dec A B x H.
    induction A.
    - destruct H.
    - simpl in *. destruct (in_dec eq_dec _ _ s B); simpl in *; destruct (eq_dec x s); subst; tauto.
Qed.

End Part1.

Load "softwareverification_homework1.v".
Module Part2.

Fixpoint product (xs : list nat) := match xs with
    | nil => S 0
    | cons y ys => y * product ys
    end.

Lemma of_singleton : forall n, product (cons n nil) = n.
Proof. intros n. simpl. induction n; simpl; [| rewrite IHn]; reflexivity. Qed.

(*Lemma plus_rightzero : forall n, n + 0 = n. induction n; simpl; [| rewrite IHn]; reflexivity. Qed.*)

Theorem of_join : forall l m, product (l ++ m) = product l * product m.
Proof.
    intros l. induction l; intro m; simpl.
    - rewrite plus_rightzero. reflexivity.
    - simpl. rewrite IHl, mult_associative. reflexivity.
Qed.

End Part2.
