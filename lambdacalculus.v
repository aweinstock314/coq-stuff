Extraction Language Haskell.

Require Export String.
Require Export MSets.

Module ListOrderedType1(O1 : OrderedType) <: OrderedType.
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
    Add Relation t ListOrderedType1.eq
        reflexivity proved by eq_refl
        symmetry proved by eq_sym
        transitivity proved by ListOrderedType1.eq_trans
        as rel_eq.

    Fixpoint lt x y := match x with
    | nil => match y with
        | nil => False
        | cons _ _ => True
        end
    | cons b bs => match y with
        | nil => False
        | cons c cs => O1.lt b c \/ (O1.eq b c /\ lt bs cs)
        end
    end.

    Lemma lt_not_refl : forall x, ~(lt x x).
        induction x.
        - exact (fun x => x).
        - destruct 1.
            + (exfalso; exact ((@StrictOrder_Irreflexive O1.t O1.lt O1.lt_strorder) a H)).
            + exact (IHx (proj2 H)).
        Qed.
    Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
        induction x as [|b bs], y as [|c cs], z as [|d ds]; simpl in *; try tauto.
        intros. destruct H as [|[Hbc Tbc]], H0 as [|[Hcd Tcd]].
        - left. apply (StrictOrder_Transitive b c d); assumption.
        - left. rewrite <- Hcd. assumption.
        - left. rewrite Hbc. assumption.
        - right. split.
            + apply (Equivalence_Transitive b c d); tauto.
            + exact (IHbs cs ds Tbc Tcd).
        Qed.
    Definition lt_strorder : StrictOrder lt := {|
        StrictOrder_Irreflexive := lt_not_refl;
        StrictOrder_Transitive := lt_trans;
        |}.

    Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
        unfold Proper, respectful. intros xs xs' Hx ys ys' Hy.
        (* I expect "rewrite Hx; rewrite Hy" to work here, but it fails with a giant message about UNDEFINED EVARS, even though I have the "Add Relation t ListOrderedType1.eq" above *)

        (*split; induction xs, xs', ys, ys'; simpl in *; try tauto.*)
        Admitted.

    Definition compare (x y : t) : comparison.
        Admitted.

    Definition compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
        Admitted.

End ListOrderedType1.
Module ListOrderedType2(O1 : OrderedType) <: OrderedType.
    Module MO := OrderedTypeFacts(O1).

    Definition t := list O1.t.

    Inductive eq' : nat -> t -> t -> Prop := eq_nil : eq' 0 nil nil | eq_inj : forall n x xs y ys, O1.eq x y -> eq' n xs ys -> eq' (S n) (x :: xs) (y :: ys).
    (* Workaround for "The kernel does not recognize yet that a parameter can be instantiated by an inductive type." *)
    Definition eq : t -> t -> Prop := fun x y => exists n, eq' n x y.

    Lemma eq_refl : forall x, eq x x.
        (*induction x; [ apply eq_nil | apply eq_inj; [apply Equivalence_Reflexive | exact IHx ]]. Qed.*)
        induction x; [ exists 0; apply eq_nil | destruct IHx as [n IHx]; exists (S n); apply eq_inj; [apply Equivalence_Reflexive | exact IHx ]]. Qed.
    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
        (*intros x y H; induction H; [ apply eq_nil | apply eq_inj; [ apply Equivalence_Symmetric | ]; assumption]. Qed.*)
        intros x y H; destruct H as [n H]; induction H.
        - exists 0; apply eq_nil.
        - destruct IHeq' as [m IHeq']; exists (S m); apply eq_inj; [ apply Equivalence_Symmetric | ]; assumption.
        Qed.
    Lemma neq_nil_l {x} {xs} : ~(eq nil (x :: xs)). destruct 1; easy. Qed.
    Lemma neq_nil_r {x} {xs} : ~(eq (x :: xs) nil). destruct 1; easy. Qed.
    Lemma eq_trans' : forall n (x y z : t), eq' n x y -> eq' n y z -> eq' n x z.
        Admitted.
    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
        Admitted.
    (*Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.*)
        (*intros x y z Hxy Hyz.
        induction Hxy.
        - destruct Hyz; [apply eq_nil | apply (eq_inj _ _ _ _ H Hyz)].
        - inversion Hyz. subst. apply eq_inj.
            + apply (Equivalence_Transitive _ _ _ H H2).*)
        (*(intros x y z Hxy Hyz).
(induction x, y, z; try easy).
(apply eq_inj).
 (inversion Hxy; inversion Hyz).
 subst.
 (apply (Equivalence_Transitive a t0 t1); assumption).

 (inversion Hxy).
 (inversion Hyz).
 subst.
*)
    Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
        Admitted.

    Definition eq_equiv : Equivalence eq := {|
        Equivalence_Reflexive := eq_refl;
        Equivalence_Symmetric := eq_sym;
        Equivalence_Transitive := eq_trans;
        |}.

    Fixpoint lt x y := match x with
    | nil => match y with
        | nil => False
        | cons _ _ => True
        end
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
        unfold Proper, respectful. intros xs xs' Hx ys ys' Hy.
        Admitted.

    Definition compare (x y : t) : comparison.
        Admitted.

    Definition compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
        Admitted.
    
End ListOrderedType2.
Module ListOrderedType3(O1 : OrderedType) <: OrderedType.
    Module MO := OrderedTypeFacts(O1).

    Definition t := list O1.t.
    Definition eq : t -> t -> Prop := Logic.eq.

    Lemma eq_refl : forall x, eq x x. intros x. apply Logic.eq_refl. Qed.
    Lemma eq_sym : forall x y : t, eq x y -> eq y x. intros x y. apply Logic.eq_sym. Qed.
    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. intros x y z. apply Logic.eq_trans. Qed.
    Definition eq_equiv : Equivalence eq := {|
        Equivalence_Reflexive := eq_refl;
        Equivalence_Symmetric := eq_sym;
        Equivalence_Transitive := eq_trans;
        |}.

    Fixpoint lt x y := match x with
    | nil => match y with
        | nil => False
        | cons _ _ => True
        end
    | cons b bs => match y with
        | nil => False
        | cons c cs => O1.lt b c \/ (O1.eq b c /\ lt bs cs)
        end
    end.

    Lemma lt_not_refl : forall x, ~(lt x x).
        induction x.
        - exact (fun x => x).
        - destruct 1.
            + (exfalso; exact ((@StrictOrder_Irreflexive O1.t O1.lt O1.lt_strorder) a H)).
            + exact (IHx (proj2 H)).
        Qed.
    Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
        induction x as [|b bs], y as [|c cs], z as [|d ds]; simpl in *; try tauto.
        intros. destruct H as [|[Hbc Tbc]], H0 as [|[Hcd Tcd]].
        - left. apply (StrictOrder_Transitive b c d); assumption.
        - left. rewrite <- Hcd. assumption.
        - left. rewrite Hbc. assumption.
        - right. split.
            + apply (Equivalence_Transitive b c d); tauto.
            + exact (IHbs cs ds Tbc Tcd).
        Qed.
    Definition lt_strorder : StrictOrder lt := {|
        StrictOrder_Irreflexive := lt_not_refl;
        StrictOrder_Transitive := lt_trans;
        |}.
    Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
        unfold Proper, respectful. intros xs xs' Hx ys ys' Hy.
        rewrite Hx, Hy. tauto.
        Qed.

    Fixpoint compare (x y : t) : comparison :=
        match (x, y) with
        | (nil, nil) => Eq
        | (_, nil) => Gt
        | (nil, _) => Lt
        | (b::bs, c::cs) => match O1.compare b c with
            | Lt => Lt
            | Eq => compare bs cs
            | Gt => Gt
            end
        end.

    Lemma lex_reduction : forall {A:Type} (f : A -> A -> comparison) b c, match f b c with Lt => Lt | Gt => Gt | Eq => f b c end = f b c.
        intros A f b c. destruct f; reflexivity. Qed.
    Lemma compare_spec' (xs ys : t) : forall (x y : O1.t), CompareSpec (eq (x::xs) (y::ys)) (lt (x::xs) (y::ys)) (lt (y::ys) (x::xs)) (compare (x::xs) (y::ys)).
        (*induction xs, ys; intros x y.*)
        induction xs, ys; intros x y; simpl; destruct (O1.compare_spec x y); match goal with
        | |- CompareSpec _ _ _ Lt => idtac "lt"; apply CompLt
        | |- CompareSpec _ _ _ Eq => idtac "eq"; apply CompEq
        | |- CompareSpec _ _ _ Gt => idtac "gt"; apply CompGt
        | _ => idtac "recursive comparison"
        end; try tauto; match goal with
        | H:(O1.eq x y) |- _ \/ (O1.eq y x /\ True) => right; apply (fun x => conj x I); apply Equivalence_Symmetric; exact H
        | _ => admit
        end.
        Show.
        Admitted.
        
        (*induction xs, ys; intros x y; destruct (O1.compare_spec x y).*)
        (*- set (H := O1.compare_spec x y). inversion H.
              +(simpl).  (rewrite H0).  (rewrite (lex_reduction O1.compare x y)).*)
    Lemma compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
        induction x as [|b bs], y as [|c cs].
        - (apply CompEq). reflexivity.
        - (apply CompLt). exact I.
        - (apply CompGt). exact I.
        - exact (compare_spec' bs cs b c).
        Qed.
    (*Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
        induction x; intros **; destruct y; simpl in *; try easy.
        destruct (O1.eq_dec a t0), (IHx y); tauto.
    Qed.*)
    Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
        Admitted.
End ListOrderedType3.

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
