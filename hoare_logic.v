(* adapted from http://www.cs.rpi.edu/~milanova/csci4450/Lecture19.pdf *)
Inductive BinaryOperator := Plus | Times.

Inductive Expr :=
    | Lit : nat -> Expr
    | Var : nat -> Expr
    | Binop : BinaryOperator -> Expr -> Expr -> Expr
    | EqualityComparison : Expr -> Expr -> Expr.
Inductive Stmt :=
    | Assign : nat -> Expr -> Stmt
    | Seq : Stmt -> Stmt -> Stmt
    | IfStmt : Expr -> Stmt -> Stmt -> Stmt
    | WhileStmt : Expr -> Stmt -> Stmt
    | Skip : Stmt.

Definition Env := nat -> nat.

Definition denote_binop (b : BinaryOperator) : (nat -> nat -> nat) := match b with
    | Plus => Nat.add
    | Times => Nat.mul
    end.

Fixpoint denote_expr (sigma : Env) (e : Expr) : nat := match e with
    | Lit e => e
    | Var x => sigma x
    | Binop b e1 e2 => denote_binop b (denote_expr sigma e1) (denote_expr sigma e2)
    | EqualityComparison e1 e2 => match Nat.eqb (denote_expr sigma e1) (denote_expr sigma e2) with true => 1 | false => 0 end
    end.

Definition bind_opt {A B} (x : option A) (f : A -> option B) : option B := match x with None => None | Some x' => f x' end.
Infix ">>=" := bind_opt (at level 70).
Definition augment_env (index : nat) (value : nat) (sigma : Env) : Env := fun n => match Nat.eqb n index with true => value | false => sigma n end.

Fixpoint denote_stmt (depth : nat) (s : Stmt) (sigma : Env) : option Env := match depth with 0 => None | S n =>
    match s with
    | Assign x e => Some (augment_env x (denote_expr sigma e) sigma)
    | Seq s1 s2 => (denote_stmt n s1 sigma) >>= (fun sigma' => denote_stmt n s2 sigma')
    | IfStmt e s1 s2 => denote_stmt n (match denote_expr sigma e with (S _) => s1 | 0 => s2 end) sigma
    | WhileStmt e s => match denote_expr sigma e with
        | (S _) => denote_stmt n s sigma >>= (fun sigma' => denote_stmt n (WhileStmt e s) sigma')
        | 0 => Some sigma
        end
    | Skip => Some sigma
    end end.
