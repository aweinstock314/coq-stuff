Module Peano.

Inductive Nat : Set := Z : Nat | S : Nat -> Nat.

(* Convertions to Coq's built-in peano naturals *)
Fixpoint nat2Nat (n : nat) : Nat := match n with 0 => Z | Coq.Init.Datatypes.S n => S (nat2Nat n) end.
Fixpoint Nat2nat (n : Nat) : nat := match n with Z => 0 | S n => Coq.Init.Datatypes.S (Nat2nat n) end.

Fixpoint plus (n m : Nat) : Nat :=
    match n with
        | Z => m
        | S n' => S (plus n' m)
    end.

(* This version is proved with a script that was written interactively for just this one property *)
Lemma plus_rightidentity' : forall n, plus n Z = n.
    intros; induction n; [
        simpl; reflexivity
        | simpl; rewrite IHn; reflexivity
    ].
    Qed.

(* This version is the Gallina proof term that was constructed by the above script, extracted with `Print plus_rightidentity'` *)
(* It explicitly juggles around dependently-typed proof objects, in a manner reminiscent of Idris proofs *)
Lemma plus_rightidentity'' : forall n, plus n Z = n.
    exact (fun n : Nat => Nat_ind
        (fun n0 : Nat => plus n0 Z = n0) eq_refl
        (fun (n0 : Nat) (IHn : plus n0 Z = n0) => eq_ind_r (fun n1 : Nat => S n1 = S n0) eq_refl IHn) n).
    Qed.

(* This version is a refactored proof script that handles most of the proofs directly, and can take hints as arguments *)
Ltac simple_nat_induction n c1 c2 := intros; induction n as [ | n IHn ]; simpl; [ c1 | rewrite IHn; c2 ]; reflexivity.
Ltac simple_nat_induction' n := simple_nat_induction n idtac idtac.

Lemma plus_rightidentity : forall n, plus n Z = n.
    simple_nat_induction' n. Qed.

Lemma plus_rightsucc : forall n m, plus n (S m) = S (plus n m).
    simple_nat_induction' n. Qed.

Theorem plus_associative : forall x y z, plus (plus x y) z = plus x (plus y z).
    simple_nat_induction' x. Qed.

(* Manual proof of commutativity *)
Theorem plus_commutative' : forall n m, plus n m = plus m n.
    intros; induction n.
    simpl; rewrite plus_rightidentity; reflexivity.
    simpl; rewrite IHn; rewrite plus_rightsucc; reflexivity.
    Qed.
(* More automated/factored proof of commutativity *)
Theorem plus_commutative : forall n m, plus n m = plus m n.
    simple_nat_induction n ltac:(rewrite plus_rightidentity) ltac:(rewrite plus_rightsucc).
    Qed.

Definition trianglenumber : Nat -> Nat := Nat_rec (fun _ => Nat) Z plus.

End Peano.
Import Peano.
