Load "ListBackedSet".

(* adapted from http://www.cs.rpi.edu/~milanova/csci4450/Lecture19.pdf *)
Module Imp.
Inductive LangType := TyNat | TyBool.
Scheme Equality for LangType.

Definition denote_type x := match x with
    | TyNat => nat
    | TyBool => bool
    end.

Inductive UnaryOperator : LangType -> Type := Not : UnaryOperator TyBool.

Inductive BinaryOperator : LangType -> LangType -> Type :=
    Plus : BinaryOperator TyNat TyNat | Times : BinaryOperator TyNat TyNat |
    And : BinaryOperator TyBool TyBool | Or : BinaryOperator TyBool TyBool |
    Eq : forall T, DecEq (denote_type T) -> BinaryOperator T TyBool |
    Lt : BinaryOperator TyNat TyBool.

Inductive Expr : LangType -> Type :=
    | Lit : forall T (x:denote_type T), Expr T
    | Var : forall T, nat -> Expr T
    | Unop : forall T, UnaryOperator T -> Expr T -> Expr T
    | Binop : forall T U, BinaryOperator T U -> Expr T -> Expr T -> Expr U.

Inductive Stmt :=
    | Assign : forall T, nat -> Expr T -> Stmt
    | Seq : Stmt -> Stmt -> Stmt
    | IfStmt : Expr TyBool -> Stmt -> Stmt -> Stmt
    | WhileStmt : Expr TyBool -> Stmt -> Stmt
    | Skip : Stmt.

Definition Env := nat -> option {T : LangType & denote_type T}.
Definition exampleEnv : Env := fun x => match x with
    | 0 => Some (existT denote_type TyNat 5)
    | 1 => Some (existT denote_type TyBool true)
    | _ => None
    end.

Definition bind_opt {A B} (x : option A) (f : A -> option B) : option B := match x with None => None | Some x' => f x' end.
Infix ">>=" := bind_opt (at level 70).

Definition null_env : Env := fun _ => None.
Definition augment_env {T} (index : nat) (value : denote_type T) (sigma : Env) : Env :=
    fun n => match Nat.eqb n index with
        | true => Some (existT denote_type T value)
        | false => sigma n
    end.

Definition denote_unop {T} (op : UnaryOperator T) : (denote_type T -> denote_type T) := match op with
    | Not => negb
    end.
Definition denote_binop {T U} (op : BinaryOperator T U) : (denote_type T -> denote_type T -> denote_type U) := match op with
    | Plus => Nat.add | Times => Nat.mul
    | And => andb | Or => orb
    | Eq _ eq_dec => fun x y => if eq_dec x y then true else false
    | Lt => Nat.ltb
    end.

Fixpoint denote_expr {T} (sigma : Env) (e : Expr T) : option (denote_type T) := match e with
    | Lit _ e => Some e
    | Var t1 x => sigma x >>= fun val => match val with existT _ t2 y =>
        match LangType_eq_dec t1 t2 with
        | left eq_t1_t2 => Some ltac:(rewrite eq_t1_t2; exact y)
        | right _ => None
        end end
    | Unop _ op e =>
        (denote_expr sigma e) >>= fun x =>
        Some (denote_unop op x)
    | Binop _ _ op e1 e2 =>
        (denote_expr sigma e1) >>= fun x =>
        (denote_expr sigma e2) >>= fun y =>
        Some (denote_binop op x y)
    end.

Fixpoint denote_stmt (depth : nat) (s : Stmt) (sigma : Env) : option Env := match depth with 0 => None | S n =>
    match s with
    | Assign _ x e => (denote_expr sigma e) >>= fun val => Some (augment_env x val sigma)
    | Seq s1 s2 => (denote_stmt n s1 sigma) >>= (fun sigma' => denote_stmt n s2 sigma')
    | IfStmt e s1 s2 => denote_expr sigma e >>= fun val => denote_stmt n (if val then s1 else s2) sigma
    | WhileStmt e s => denote_expr sigma e >>= fun val => match val with
        | true => denote_stmt n s sigma >>= (fun sigma' => denote_stmt n (WhileStmt e s) sigma')
        | false => Some sigma
        end
    | Skip => Some sigma
    end end.
End Imp.
Import Imp.
