(* BinTree the type of binary trees that store values at each node, and nothing at the leaves *)
Inductive BinTree {A : Type} := Leaf : BinTree | Branch : A -> BinTree -> BinTree -> BinTree.

(* (Bin_elem x t) is a proof that x is in t, and the structure of the proof is the path taken to reach it *)
Inductive Bin_elem {A : Type} : A -> BinTree -> Prop :=
    | Bin_elem_exact : forall x l r, Bin_elem x (Branch x l r)
    | Bin_elem_left : forall x y l r, Bin_elem x l -> Bin_elem x (Branch y l r)
    | Bin_elem_right : forall x y l r, Bin_elem x r -> Bin_elem x (Branch y l r).

(* Bin_elem' makes use of a decideable equality procedure, and computes whether or not the element is in the tree, returning a type.
    It doesn't explicitly store the path in a traversable form, the path is implicit in the structure of its computation. *)
Fixpoint Bin_elem' {A : Type} {eq_dec : forall x y : A, {x = y} + {x <> y}} (x : A) (t : BinTree) : Prop :=
    match t with
    | Leaf => False
    | Branch y l r => match eq_dec x y with
        | left _ => True
        | right _ => @ Bin_elem' A eq_dec x l \/ @ Bin_elem' A eq_dec x r
        end
    end.

(* Both formulations are equivalent, but Bin_elem has fewer dependencies (since it doesn't need eq_dec) *)
Theorem Bin_elems_equiv : forall A eq_dec (x : A) t, Bin_elem x t <-> @ Bin_elem' A eq_dec x t.
    (* manual proof *)
    intros a eq_dec x t.
    induction t.
    - split; inversion 1.
    - simpl. destruct (eq_dec x a0).
        + split.
            * tauto.
            * intro. rewrite e. apply Bin_elem_exact.
        + split.
            * inversion 1; tauto.
            * inversion 1.
                -- apply Bin_elem_left. exact (proj2 IHt1 H0).
                -- apply Bin_elem_right. exact (proj2 IHt2 H0).
    Restart.
    (* proof with match goal and explicit inversion *)
    intros a eq_dec x t.
    induction t; split; simpl; match goal with
    | |- Bin_elem _ Leaf -> _ => inversion 1
    | |- False -> _ => inversion 1
    | |- context[eq_dec ?x ?y] => destruct (eq_dec x y); match goal with
        | |- _ -> True => exact (fun _ => I)
        | |- Bin_elem x (Branch y ?l ?r) -> _ => inversion 1; tauto
        | e:(x = y) |- _ -> Bin_elem x (Branch y _ _) => intro; rewrite e; apply Bin_elem_exact
        | |- Bin_elem' x ?l \/ Bin_elem' x ?r -> _ => destruct 1; [apply Bin_elem_left | apply Bin_elem_right]; tauto
        end
    end.
    Restart.
    (* more automated proof *)
    intros a eq_dec x t.
    induction t; split; simpl; try easy; match goal with
    | |- context[eq_dec ?x ?y] => destruct (eq_dec x y); match goal with
        | |- Bin_elem x (Branch y ?l ?r) -> _ => inversion 1; tauto
        | e:(x = y) |- _ -> Bin_elem x (Branch y _ _) => intro; rewrite e; apply Bin_elem_exact
        | |- Bin_elem' x ?l \/ Bin_elem' x ?r -> _ => destruct 1; [apply Bin_elem_left | apply Bin_elem_right]; tauto
        end
    end.
    Qed.
