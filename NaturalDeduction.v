Require Import List.
From QuickChick Require Import QuickChick.
Import ListNotations.

Module IPL.
(* rules for Gentzen's Intuitionistic Propositional Logic transcribed from http://www.iep.utm.edu/nat-ded/ *)

Inductive AST :=
    | Bot : AST
    | Neg : AST -> AST
    | And : AST -> AST -> AST
    | Or : AST -> AST -> AST
    | Imp : AST -> AST -> AST
    .
Derive (GenSized, Shrink, Arbitrary, Show) for AST.

Inductive Derivation : list AST -> AST -> Prop :=
    | BotElim : forall gamma phi, In Bot gamma -> Derivation gamma phi
    | NegElim : forall gamma phi, In phi gamma -> In (Neg phi) gamma -> Derivation gamma Bot
    | NegIntro : forall gamma phi, Derivation (cons phi gamma) Bot -> Derivation gamma (Neg phi)
    | AndIntro : forall gamma phi psi, In phi gamma -> In psi gamma -> Derivation gamma (And phi psi)
    | AndElimL : forall gamma phi psi, In (And phi psi) gamma -> Derivation gamma phi
    | AndElimR : forall gamma phi psi, In (And phi psi) gamma -> Derivation gamma psi
    | ImpElim : forall gamma phi psi, In phi gamma -> In (Imp phi psi) gamma -> Derivation gamma psi
    | ImpIntro : forall gamma phi psi, Derivation (cons phi gamma) psi -> Derivation gamma (Imp phi psi)
    | OrIntroL : forall gamma phi psi, In phi gamma -> Derivation gamma (Or phi psi)
    | OrIntroR : forall gamma phi psi, In psi gamma -> Derivation gamma (Or phi psi)
    | OrElim : forall gamma delta psi phi chi, Derivation (cons psi gamma) chi -> Derivation (cons phi delta) chi -> Derivation ([Or phi psi]++gamma++delta) chi
    .

Example derive_true : Derivation [] (Neg Bot).
Proof. apply NegIntro, BotElim; simpl; tauto. Defined.

Theorem soundness : ~Derivation [] Bot.
Proof. inversion 1; subst; easy. Defined.

Fixpoint interp_ast (a : AST) : Prop := match a with
    | Bot => False
    | Neg x => ~(interp_ast x)
    | And x y => interp_ast x /\ interp_ast y
    | Or x y => interp_ast x \/ interp_ast y
    | Imp x y => interp_ast x -> interp_ast y
    end.

End IPL.

Module PHOASLam.

Module Attempt1.
Inductive Expr (V : Type -> Type) : Type -> Type :=
    | Const : forall A, A -> Expr V A
    | Var : forall A, V A -> Expr V A
    | App : forall A B, Expr V (A -> B) -> Expr V A -> Expr V B
    | Abs : forall A B, (V A -> Expr V B) -> Expr V (A -> B).

(* with recursion schemes *)
Definition eval' A : (Expr (fun x => x) A) -> A.
induction 1.
- exact a.
- exact v.
- exact (IHX1 IHX2).
- exact X.
Defined.

(* with explicit structural recursion *)
Fixpoint eval {A} (e : Expr (fun x => x) A) : A := match e with
    | Const _ a => a
    | Var _ v => v
    | App _ _ e1 e2 => (eval e1) (eval e2)
    | Abs A B f => fun e => eval (f e)
    end.

Definition const {V} {A} (x : A) := Const V A x.
Definition var {V} {A} (x : V A) := Var V A x.
Definition app {V} {A B} e1 e2 := App V A B e1 e2.
Definition abs {V} {A B} (x : V A -> Expr V B) := Abs V A B x.

Definition embed_id {V} {A} : Expr V (A -> A) := abs (fun x => var x).
End Attempt1.

Module Attempt2.
Inductive Expr {T : Type} {Inj : Type -> T} {Arr : Type -> Type -> T} (V : Type -> Type) : T -> Type :=
  | Const : forall A : Type, A -> Expr V (Inj A)
  | Var : forall A : Type, V A -> Expr V (Inj A)
  | App : forall A B : Type, Expr V (Arr A B) -> Expr V (Inj A) -> Expr V (Inj B)
  | Abs : forall A B : Type, (V A -> Expr V (Inj B)) -> Expr V (Arr A B)
    .
Definition Expr' := @Expr Type id (fun a b => (a -> b)).

Fixpoint eval' {A} (e : Expr' (fun x => x) A) : A := match e with
    | Const _ a => a
    | Var _ v => v
    | App _ _ e1 e2 => (eval' e1) (eval' e2)
    | Abs A B f => fun e => eval' (f e)
    end.

Definition const {T} {Inj} {Arr} {V} {A} (x : A) : @Expr T Inj Arr V (Inj A) := Const V A x.
Definition var {T} {Inj} {Arr} {V} {A} (x : V A) : @Expr T Inj Arr V (Inj A) := Var V A x.
Definition app {T} {Inj} {Arr} {V} {A B} e1 e2 : @Expr T Inj Arr V (Inj B) := App V A B e1 e2.
Definition abs {T} {Inj} {Arr} {V} {A B} (x : V A -> Expr V (Inj B)) : @Expr T Inj Arr V (Arr A B) := Abs V A B x.

Definition embed_id {T} {Inj} {Arr} {V} {A} : @Expr T Inj Arr V (Arr A A) := abs (fun x => var x).
End Attempt2.

Module Attempt3.
Inductive Expr {T : Type -> Type} {Inj : forall A, T A} {Arr : forall A B, {C & T C}} (V : Type -> Type) : {C & T C} -> Type :=
    | Const : forall A, A -> Expr V (existT _ _ (Inj A))
    | Var : forall A, V A -> Expr V (existT _ _ (Inj A))
    | App : forall A B C, (T C = projT1 (Arr A B)) -> Expr V (Arr A B) -> Expr V (existT _ _ (Inj A)) -> Expr V (existT _ _ (Inj B))
    | Abs : forall A B, (V A -> Expr V (existT _ _ (Inj B))) -> Expr V (Arr A B).

Definition Expr' := @Expr (fun x => Type) (fun x => x) (fun a b => existT _ (a -> b) (a -> b)).

Definition const {T} {Inj} {Arr} {V} {A} (x : A) : @Expr T Inj Arr V (existT _ _ (Inj A)) := Const V A x.
Definition var {T} {Inj} {Arr} {V} {A} (x : V A) : @Expr T Inj Arr V (existT _ _ (Inj A)) := Var V A x.
Definition app {T} {Inj} {Arr} {V} {A B C} {H} (e1 : @Expr T Inj Arr V (Arr A B)) e2 : @Expr T Inj Arr V (existT _ _ (Inj B)) := App V A B C H e1 e2.
Definition abs {T} {Inj} {Arr} {V} {A B} (x : V A -> Expr V (existT _ _ (Inj B))) : @Expr T Inj Arr V (Arr A B) := Abs V A B x.

Definition embed_id {T} {Inj} {Arr} {V} {A} : @Expr T Inj Arr V (Arr A A) := abs (fun x => var x).

Fixpoint eval' {A} (e : Expr' (fun x => x) A) : projT1 A := match e with
    | Const _ a => a
    | Var _ v => v
    | App _ _ _ _ e1 e2 => (eval' e1) (eval' e2)
    | Abs A B f => fun e => eval' (f e)
    end.

(* Compute (eval' embed_id tt, eval' embed_id 42). *)
End Attempt3.

Include Attempt3.

End PHOASLam.
