Require Import Vector.
Require Import Omega.

(* https://en.wikipedia.org/wiki/Primitive_recursion#Definition *)
(* PrimRec's index is intended to correspond to arity *)
Inductive PrimRec : nat -> Set :=
    | Zero : PrimRec 0
    | Succ : PrimRec 1
    | Proj : forall (n i : nat), (i < n) -> PrimRec n
    | Comp : forall k m, PrimRec k -> Vector.t (PrimRec m) k -> PrimRec m
    | Rec : forall k, PrimRec k -> PrimRec (2 + k) -> PrimRec (1 + k)
    .

Fixpoint arity_to_type (k : nat) : Set := match k with 0 => nat | (S k') => (nat -> arity_to_type k') end.

Fixpoint variadic_const n : arity_to_type (S n) := match n with 0 => (fun x => x) | S n' => (fun x _ => variadic_const n' x) end.

Example variadic_const_demo_0 : variadic_const 5 10 20 30 40 50 60 = 10. reflexivity. Qed.

Definition proj_denote n i (H : i < n) : arity_to_type n.
revert i H; induction n; intros i H.
- omega.
- destruct i.
+ apply variadic_const.
+ intros x; apply (IHn i); omega.
Defined.

Definition vec_S_hd {A} {n} (xs : Vector.t A (S n)) : A := Vector.caseS (fun _ _ => A) (fun y _ _ => y) xs.
Definition vec_S_tl {A} {n} (xs : Vector.t A (S n)) : Vector.t A n := ltac:(inversion xs; assumption).

Definition vec_apply {A B} n (fs : Vector.t (A -> B) n) (xs : Vector.t A n) : Vector.t B n.
induction n; constructor.
- exact (vec_S_hd fs (vec_S_hd xs)).
- exact (IHn (vec_S_tl fs) (vec_S_tl xs)).
Defined.

Fixpoint vec_replicate {A} n (x : A) : Vector.t A n := match n with 0 => nil _ | S n' => cons A x n' (vec_replicate n' x) end.

Definition variadic_uncurry k (f : arity_to_type k) (xs : Vector.t nat k) : nat.
induction k.
- exact f.
- exact (IHk (f (vec_S_hd xs)) (vec_S_tl xs)).
Defined.

Definition variadic_curry k (f : Vector.t nat k -> nat) : arity_to_type k.
induction k.
- exact (f (nil _)).
- intros x; exact (IHk (fun xs => f (cons nat x k xs))).
Defined.

Fixpoint primrec_denote k (f : PrimRec k) : arity_to_type k := match f with
    | Zero => 0
    | Succ => S
    | Proj n i H => proj_denote n i H
    | Comp k' m f' gs =>
        let gs' := Vector.map (fun g => variadic_uncurry m (primrec_denote m g)) gs in
        let f'' := variadic_uncurry k' (primrec_denote k' f') in
        variadic_curry m (fun h => f'' (vec_apply _ gs' (vec_replicate k' h)))
    | Rec k' f g => fix h (x : nat) : arity_to_type k' := match x with
        | 0 => primrec_denote _ f
        | S y => variadic_curry _ (fun xs => variadic_uncurry _ (primrec_denote _ g y (variadic_uncurry _ (h y) xs)) xs)
        end
    end.

Definition comp1 {n} : PrimRec 1 -> PrimRec n -> PrimRec n := fun x y => Comp 1 n x (cons _ y _ (nil _)).

Definition PR_plus : PrimRec 2 := Rec 1 (Proj 1 0 ltac:(omega)) (comp1 Succ (Proj 3 1 ltac:(omega))).

Example PR_plus_demo_0 : primrec_denote _ PR_plus 22 7 = 29. reflexivity. Qed.

Lemma PR_plus_builtin_plus_compat : forall x y, primrec_denote _ PR_plus x y = x + y.
induction x; intros y.
- reflexivity.
- simpl in *; rewrite (IHx y);  reflexivity.
Qed.

Definition PR_pred : PrimRec 1 := Rec _ Zero (Proj 2 0 ltac:(omega)).

Lemma PR_pred_builtin_pred_compat : forall x, primrec_denote _ PR_pred x = pred x.
destruct x; reflexivity.
Qed.

Definition PR_swap : PrimRec 2 -> PrimRec 2 := fun x => Comp _ _ x (cons _ (Proj 2 1 ltac:(omega)) _ (cons _ (Proj 2 0 ltac:(omega)) _ (nil _))).

Lemma PR_swap_correct : forall f x y, primrec_denote _ (PR_swap f) x y = primrec_denote _ f y x. reflexivity. Qed.

Definition PR_sub : PrimRec 2 := PR_swap (Rec _ (Proj 1 0 ltac:(omega)) (comp1 PR_pred (Proj 3 1 ltac:(omega)))).

Lemma PR_sub_builtin_sub_compat : forall x y, primrec_denote _ PR_sub x y = x - y.
induction y; simpl in *.
- apply minus_n_O.
- rewrite IHy, PR_pred_builtin_pred_compat, Nat.sub_succ_r; reflexivity.
Qed.
