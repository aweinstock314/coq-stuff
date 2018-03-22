Extraction Language Haskell.

Require Export String.
Require Export MSets.

Module ListOrderedType(O1 : OrderedType) <: OrderedType.
    Module MO := OrderedTypeFacts(O1).

    Definition t := list O1.t.

    Fixpoint eq x y := match x with
    | nil => match y with
        | nil => True
        | _ => False
        end
    | cons b bs => match y with
        | nil => False | cons c cs => O1.eq b c /\ eq bs cs
        end
    end.

    Lemma eq_refl : forall x, eq x x.
        induction x.
        - reflexivity.
        - split.
            + apply Equivalence_Reflexive.
            + exact IHx.
        Qed.

    Lemma cons_neq : forall bs b, ~(eq bs (b :: bs)).
    induction bs; intros b H.
    - inversion H.
    - destruct (O1.eq_dec a b).
        + exact (IHbs a (proj2 H)).
        + exact (n (proj1 H)).
    Qed.

    Lemma eq_sym' : forall bs cs b c, eq (b :: bs) (c :: cs) -> eq (c :: cs) (b :: bs).
    induction bs as [|x xs], cs as [|y ys]; intros b c e; try split; inversion e; match goal with
    | H : O1.eq b c |- O1.eq c b => apply Equivalence_Symmetric; exact H
    | |- eq nil nil => reflexivity
    | H : eq (x :: xs) (y :: ys) |- eq (y :: ys) (x :: xs) => exact (IHxs _ _ _ H)
    | H : eq ?foo ?bar |- _ => inversion H
    end. Qed.

    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    intros x y e.
    induction x, y; try inversion e.
    - reflexivity.
    - split.
        + apply Equivalence_Symmetric. assumption.
        + exact (proj2 (eq_sym' _ _ _ _ e)).
    Qed.

    Lemma eq_trans' : forall bs cs ds b c d, eq (b :: bs) (c :: cs) -> eq (c :: cs) (d :: ds) -> eq (b :: bs) (d :: ds).
        induction bs as [|x xs], cs as [|y ys], ds as [|z zs]; intros b c d ebc ecd; split; simpl in *; match goal with
        | |- True => exact I
        | H : (_ /\ False) |- _ => destruct (proj2 H)
        | |- eq nil nil => reflexivity
        | H : (O1.eq b c /\ _), H' : (O1.eq c d /\ _) |- O1.eq b d => exact (Equivalence_Transitive b c d (proj1 H) (proj1 H'))
        | _ => exact (IHxs ys zs x y z (proj2 ebc) (proj2 ecd))
        end. Qed.

    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
        intros x y z exy eyz. induction x as [|b bs],y as [|c cs],z as [|d ds]; match goal with
        | |- eq nil nil => reflexivity
        | H : eq nil (cons _ _) |- _ => inversion H
        | H : eq (cons _ _) nil |- _ => inversion H
        | _ => exact (eq_trans' _ _ _ _ _ _ exy eyz)
        end. Qed.

    (*Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
        intros x y.
        destruct x as [|b bs]; [|revert b bs]; induction y as [|c cs]; try intros b bs.
        - left. reflexivity.
        - right. intro H. inversion H.
        - right. intro H. inversion H.
        - destruct (O1.eq_dec b c).
            + destruct (IHcs b bs).
            * right. intro H. destruct (cons_neq _ _ (eq_trans _ _ _ (eq_sym _ _ e0) H)).
            * 
            (*+ right. intro H. exact (n (proj1 H)).*) *)
    Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
        induction x; intros **; destruct y; simpl in *; auto.
        destruct (O1.eq_dec a t0), (IHx y); tauto.
    Qed.

    Definition eq_equiv : Equivalence eq := {|
        Equivalence_Reflexive := eq_refl;
        Equivalence_Symmetric := eq_sym;
        Equivalence_Transitive := eq_trans;
        |}.

    Fixpoint lt x y := match x with
    | nil => True
    | cons b bs => match y with
        | nil => False
        | cons c cs => O1.lt b c \/ (O1.eq b c /\ lt bs cs)
        end
    end.

    Lemma lt_not_refl : forall x, ~(lt x x).
        Admitted.
    Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
        Admitted.
    Definition lt_strorder : StrictOrder lt := {|
        StrictOrder_Irreflexive := lt_not_refl;
        StrictOrder_Transitive := lt_trans;
        |}.

    Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
        Admitted.

    Definition compare (x y : t) : comparison.
        Admitted.

    Definition compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
        Admitted.

End ListOrderedType.

CoInductive Stream (A : Set) : Set := Seq : A -> Stream A -> Stream A.
Definition nats := (cofix from (n : nat) : Stream nat := Seq nat n (from (S n))) O.
Fixpoint take {A} (n : nat) (s : Stream A) := match n with O => nil | S n' => match s with Seq _ x xs => cons x (take n' xs) end end.

Definition Name := string.
Inductive Expr : Set := Var : Name -> Expr | App : Expr -> Expr -> Expr | Lambda : Name -> Expr -> Expr.

Definition question2point2expression :=
    let e1 := (Lambda "x" (Lambda "y" (Var "x")))%string in
    let e2 := (Lambda "x" (App (Var "z") (Var "x")))%string in
    (App e1 (Lambda "z" (App (App e1 (Var "z")) (App e2 e2))))%string.

Eval compute in question2point2expression.

(*Definition replaceVar' (x : Name) (e : Expr) (freshNames : Stream Name) (E : Expr) : (Stream Name, Expr) :=*)

(*Definition replaceVar : (Name, Expr) -> (Stream Name, Expr) -> (Stream Name, Expr) :=*)
