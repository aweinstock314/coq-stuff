Inductive Exp := ConstE : nat -> Exp | BinopE : (nat -> nat -> nat) -> (Exp -> Exp -> Exp).
Inductive StackOp := PushS : nat -> StackOp | BinopS : (nat -> nat -> nat) -> StackOp.

Fixpoint evalExp e := match e with
    | ConstE n => n
    | BinopE f e1 e2 => f (evalExp e1) (evalExp e2)
    end.

Definition builder A := list A -> list A.
Definition build {A} (b : builder A) : list A := b nil.
Definition singleton {A} (x : A) : builder A := cons x.
Definition append {A} (x y : builder A) : builder A := fun z => x (y z).
Fixpoint prefix {A} (xs : list A) : builder A := match xs with nil => fun a => a | cons y ys => append (singleton y) (prefix ys) end.

Require Import Setoid.
Lemma build_prefix_id : forall A (xs : list A), build (prefix xs) = xs.
    intros a xs; induction xs; [|rewrite <- IHxs at 2]; reflexivity. Qed.
Lemma prefix_nil_id : forall A (xs : list A), prefix xs nil = xs.
    intros a xs; induction xs; [|rewrite <- IHxs at 2]; reflexivity. Qed.

Theorem append_assoc : forall A (x y z : builder A), append x (append y z) = append (append x y) z.
    intros A x y z. unfold append. reflexivity. Qed.

Fixpoint compile e := match e with
    | ConstE n => singleton (PushS n)
    | BinopE f e1 e2 => append (append (compile e2) (compile e1)) (singleton (BinopS f))
    end.

(*Eval cbn in compile (BinopE mult (BinopE plus (ConstE 2) (ConstE 3)) (ConstE 4)) nil.*)

Fixpoint evalStackM (prog : list StackOp) (stack : list nat) := (match prog with
    | PushS n :: prog' => evalStackM prog' (n :: stack)
    | BinopS f :: prog' => match stack with
        | x :: y :: stack' => evalStackM prog' (f x y :: stack')
        | _ => None
        end
    | nil => match stack with
        | x :: _ => Some x
        | nil => None
        end
    end)%list.

Theorem compile_correct : forall e p s, evalStackM ((compile e) p) s = evalStackM p (evalExp e :: s)%list.
    intros e. induction e; intros p s.
    - reflexivity.
    - cbn. unfold append. rewrite IHe2, IHe1. reflexivity.
    Qed.
