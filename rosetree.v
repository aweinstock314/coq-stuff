(*Fixpoint map {A B} (f : A -> B) xs := match xs with
    | nil => nil
    | cons x xs => cons (f x) (map f xs)
    end.*)
Load "ListBackedSet.v".
Import ListBackedSet.
Import ListBackedSet'.

Lemma le_trans : forall x y z, x <= y -> y <= z -> x <= z.
    induction x, y, z; try easy; intros Hxy Hyz.
    - apply le_0_n.
    - exact (le_n_S _ _ (IHx y z (le_pred _ _ Hxy) (le_pred _ _ Hyz))).
    Qed.

Inductive RoseTree (A : Type) := MkRoseTree : A -> list (RoseTree A) -> RoseTree A.
Arguments MkRoseTree [A] x xs.

(* A simple fixpoint fails because it's not structurally recursive *)
Fail Fixpoint mapRoseTree {A B} (f : A -> B) (tree : RoseTree A) {struct tree} := match tree with
    MkRoseTree x xs => MkRoseTree (f x) (map (mapRoseTree f) xs)
    end.

Definition numchildren {A} (tree : RoseTree A) := match tree with MkRoseTree _ xs => length xs end.
Definition numchildren_rel {A} (t1 t2 : RoseTree A) := numchildren t1 < numchildren t2.

Lemma numchildren_rel_wf' : forall A n (t : RoseTree A), numchildren t <= n -> Acc numchildren_rel t.
Proof.
    induction n; intros [x xs] H; apply Acc_intro; intros [y ys] H'.
    - unfold numchildren_rel in *. simpl in *. inversion H. rewrite H1 in H'. inversion H'.
    - apply IHn.
    unfold numchildren_rel in H'. simpl in *. unfold lt in *.
    inversion H.
        + rewrite H1 in H'. exact (le_pred _ _ H').
        + subst. inversion H1.
            * exact (le_S_n _ _ (le_S _ _ H')).
            * exact (le_S _ _ (le_S_n _ _ (le_S _ _ (le_trans _ _ _ H' H0)))).
Defined.

Theorem numchildren_rel_wf : forall A, well_founded (@ numchildren_rel A).
Proof. intros A [x xs]. eapply numchildren_rel_wf'. apply le_n. Defined.

Definition mapRoseTree {A B} (f : A -> B) : RoseTree A -> RoseTree B.
    (*destruct tree as [x xs].*)
    (*Check (Fix (numchildren_rel_wf A) (fun _ => RoseTree B)) (fun t rec => _).*)
    apply (Fix (numchildren_rel_wf A)). intros [x xs] H. apply MkRoseTree.
    - exact (f x).
    - eapply map. 2:exact xs.
    Abort.

Definition children {A} (tree : RoseTree A) := match tree with MkRoseTree _ xs => xs end.
Inductive Child {A} : RoseTree A -> RoseTree A -> Prop := Direct : forall t1 t2, Elem t1 (children t2) -> Child t1 t2 | Indirect : forall t1 t2 t3, Elem t1 (children t2) -> Child t2 t3 -> Child t1 t3.
Fixpoint Child' {A} (t1 t2 : RoseTree A) := match t2 with
    | MkRoseTree _ nil => False
    | MkRoseTree _ (x :: xs) => t1 = x \/ Child' t1 x \/ Elem t1 xs
    end.
Inductive Child'' {A} : nat -> RoseTree A -> RoseTree A -> Prop :=
    | Direct' : forall t1 t2, Elem t1 (children t2) -> Child'' 0 t1 t2
    | Indirect' : forall t1 t2 t3 n, Elem t1 (children t2) -> Child'' n t2 t3 -> Child'' (S n) t1 t3.

Goal forall A a (x : RoseTree A), ~Child' x (MkRoseTree a nil).
    intros A a x H. inversion H. Qed.
(*Goal forall A a (x : RoseTree A), ~Child x (MkRoseTree a nil).
    intros A a [x xs] H. induction xs.
    - inversion H; subst.
        + inversion H0.*)
Lemma not_Child''_nil : forall A a n (x : RoseTree A), ~Child'' n x (MkRoseTree a nil).
    intros A a n.
    induction n; intros x H.
    - inversion H. inversion H0.
    - inversion H. exact (IHn _ H2).
    Qed.

(*Goal forall A (t1 t2 : RoseTree A), Child t1 t2 <-> Child' t1 t2.
    intros A [x xs] [y ys]. split.
    - (induction ys).  (simpl).  intro H.*)

(*Lemma Child_wf' : forall A (t1 t2 : RoseTree A), Child t1 t2 -> Acc Child t2.
    intros A [x xs] [y ys] H.
    inversion H; subst; apply Acc_intro; intros [z zs] H'; simpl in *.
    - induction ys.
        + inversion H0.
        + apply IHys.
            *
*)
(*Theorem Child_wf : forall A, well_founded (@ Child A).
    intros A [x xs]. apply Acc_intro. intros [y ys] H. inversion H; subst; simpl in *.
    - (* Direct *) induction xs; inversion H0; subst; apply IHxs.
        +
*)
(*Theorem Child'_wf : forall A, well_founded (@ Child' A).
    intros A [x xs]. constructor; induction xs; intros [y ys] H. 
    - inversion H.
    - apply IHxs.*)

Definition depth {A} (t1 : RoseTree A) : nat := (fix depth_aux tree acc : nat := match tree with
    MkRoseTree _ children => (fix reclist xs acc' : nat := match xs with
        | nil => acc'
        | cons y ys => reclist ys (max (depth_aux y (S acc)) acc')
        end) children acc
    end) t1 0.

Fixpoint testDepth n : RoseTree True := match n with 0 => MkRoseTree I nil | S n' => MkRoseTree I (cons (testDepth n') nil) end.

Example foo1 : depth (testDepth 0) = 0. reflexivity. Qed.
Example foo2 : depth (testDepth 1) = 1. reflexivity. Qed.
Example foo3 : depth (testDepth 5) = 5. reflexivity. Qed.

Definition shallower {A} (t1 t2 : RoseTree A) := depth t1 < depth t2.

Theorem shallower_wf : forall A, well_founded (@ shallower A).
    intros A [x xs]. constructor. intros [y ys] H.
    Abort.

Theorem Child''_wf : forall A n, well_founded (@ Child'' A n).
    intros A n t. constructor. revert t.
    induction n; intros [x xs] [y ys] H; swap 1 2.
    - inversion H; subst. destruct (IHn _ _ H2).
    (*- (* (induction xs).
        + (contradict H). (apply not_Child''_nil).
        + *)
    revert H; revert xs; revert x; induction ys; intros x xs H.
    + constructor.  (intros [z zs] H').  (contradict H').  (apply not_Child''_nil).
    +
    *)
    Abort.

Definition RoseTree_rect' (A : Type) (P : RoseTree A -> Type) (Q : list (RoseTree A) -> Type)
    (H : forall x xs, Q xs -> P (MkRoseTree x xs))
    (H' : Q nil) (H'' : forall x xs, Q xs -> Q (cons x xs)) : forall t, P t.
Proof.
    intros [x xs]. apply H. induction xs.
    - exact H'.
    - apply H''. exact IHxs.
Defined.

Fixpoint RoseTree_rect'' (A : Type) (P : RoseTree A -> Type) (Q : list (RoseTree A) -> Type)
    (H : forall x xs, Q xs -> P (MkRoseTree x xs))
    (H' : Q nil) (H'' : forall x xs, P x -> Q xs -> Q (cons x xs)) (t : RoseTree A) : P t.
Proof.
    destruct t as [x xs].
    apply H. induction xs.
    - exact H'.
    - apply H''.
        + exact (RoseTree_rect'' A P Q H H' H'' a).
        + exact IHxs.
Defined.

Definition mapRoseTree {A B} (f : A -> B) (tree : RoseTree A) : RoseTree B.
    refine (RoseTree_rect'' A (fun _ => RoseTree B) (fun _ => list (RoseTree B)) _ _ _ tree).
    - intros x xs ys. exact (MkRoseTree (f x) ys).
    - exact nil.
    - intros a xs b ys. exact (cons b ys).
Defined.

(* Compute mapRoseTree (fun x => 5) (testDepth 3). *)
