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

Record TypeSystem := {
    T : Type -> Type; (* typing derivations, indexed over the type of constants *)
    Inj : forall A, T A; (* injecting a constant *)
    Arr : forall (A B : Type), {C & T C}; (* the arrow constructor *)
    }.

Definition ShallowSimpleType := {|
    T := fun _ => Type;
    Inj := fun x => x;
    Arr := fun a b => existT _ (a -> b) (a -> b);
    |}.

Definition Untyped := {|
    T := fun _ => unit;
    Inj := fun _ => tt;
    Arr := fun unit unit => existT _ unit tt;
    |}.

Module Attempt3.
Inductive Expr (TS : TypeSystem) (V : Type -> Type) : {C & T TS C} -> Type :=
    | Const : forall A, A -> Expr TS V (existT _ _ (Inj TS A))
    | Var : forall A, V A -> Expr TS V (existT _ _ (Inj TS A))
    | App : forall A B C, (T TS C = projT1 (Arr TS A B)) -> Expr TS V (Arr TS A B) -> Expr TS V (existT _ _ (Inj TS A)) -> Expr TS V (existT _ _ (Inj TS B))
    | Abs : forall A B, (V A -> Expr TS V (existT _ _ (Inj TS B))) -> Expr TS V (Arr TS A B).

Definition const {TS} {V} {A} (x : A) : Expr TS V (existT _ _ (Inj TS A)) := Const TS V A x.
Definition var {TS} {V} {A} (x : V A) : Expr TS V (existT _ _ (Inj TS A)) := Var TS V A x.
Definition app {TS} {V} {A B C} {H} (e1 : Expr TS V (Arr TS A B)) e2 : Expr TS V (existT _ _ (Inj TS B)) := App TS V A B C H e1 e2.
Definition abs {TS} {V} {A B} (x : V A -> Expr TS V (existT _ _ (Inj TS B))) : Expr TS V (Arr TS A B) := Abs TS V A B x.

Definition embed_id {TS} {V} {A} : Expr TS V (Arr TS A A) := abs (fun x => var x).

Fixpoint eval {A} (e : Expr ShallowSimpleType (fun x => x) A) : projT1 A := match e with
    | Const _ a => a
    | Var _ v => v
    | App _ _ _ _ e1 e2 => (eval e1) (eval e2)
    | Abs A B f => fun e => eval (f e)
    end.

(* Compute (eval embed_id tt, eval embed_id 42). *)

Definition UntypedExpr (V : Type -> Type) := Expr Untyped V (existT _ (unit : Type) tt).

Definition uapp {V} (e1 e2 : UntypedExpr V) : UntypedExpr V.
Proof. refine (App Untyped V unit unit unit _ e1 e2); simpl; reflexivity. Defined.

Definition selfapply {V} : UntypedExpr V := abs (fun x => uapp (var x) (var x)).
Definition diverge {V} : UntypedExpr V := uapp selfapply selfapply.

Definition betaOpt {TS} {A} {U V : Type -> Type} (e : Expr TS (fun x => Expr TS (fun _ => x) (existT _ A (Inj TS A))) (existT _ A (Inj TS A))) : option (Expr TS V (existT _ A (Inj TS A))).
    refine (match e with
    | App A B C q (Abs a b E1) E2 => Some _
    | _ => None
    end).
    Abort.
End Attempt3.

Module Attempt4.

Ltac with_sigT x := match goal with
    (*| e : _ = projT1 x |- _ => let H := fresh in set (H := projT2 x); rewrite <- e in H; exact H*)
    | e : _ = projT1 x |- _ => exact (eq_rect_r _ (projT2 x) e)
    (*| e : _ = projT1 x |- _ => exact (eq_rect (projT1 x) (fun y => _ y) (projT2 x) _ (eq_sym e))*)
    (*| e : _ = projT1 x |- _ => exact (match eq_sym e in (_ = y) return (_ y) with eq_refl => projT2 x end)*)
    end.
Inductive Expr (TS : TypeSystem) (V : Type -> Type) (C : Type) : T TS C -> Type :=
    | Const : C -> Expr TS V C (Inj TS C)
    | Var : V C -> Expr TS V C (Inj TS C)
    | App : forall A B (e : B = projT1 (Arr TS A C)), Expr TS V B ltac:(with_sigT (Arr TS A C)) -> Expr TS V A (Inj TS A) -> Expr TS V C (Inj TS C)
    | Abs : forall A B (e : C = projT1 (Arr TS A B)), (V A -> Expr TS V B (Inj TS B)) -> Expr TS V C ltac:(with_sigT (Arr TS A B)).

Definition const {TS} {V} {A} (x : A) : Expr TS V A (Inj TS A) := Const TS V A x.
Definition var {TS} {V} {A} (x : V A) : Expr TS V A (Inj TS A) := Var TS V A x.
Definition app {TS} {V} {A B C} {H : C = projT1 (Arr TS A B)} (e1 : Expr TS V C ltac:(with_sigT (Arr TS A B))) e2 : Expr TS V B (Inj TS B) := App TS V B A C H e1 e2.
Definition abs {TS} {V} {A B C} {H : C = projT1 (Arr TS A B)} (x : V A -> Expr TS V _ (Inj TS B)) : Expr TS V _ ltac:(with_sigT (Arr TS A B)) := Abs TS V C A B H x.

Definition embed_id {TS} {V} {A C} {H : C = projT1 (Arr TS A A)} : Expr TS V C ltac:(with_sigT (Arr TS A A)) := abs (fun x => var x).

Definition ShallowSimpleTypedExpr (V : Type -> Type) (A : Type) : Type := Expr ShallowSimpleType V A A.

(* Unfortunately, because rewriting by an equality is used before the recursive call, it's not structurally recursive *)
Fail Fixpoint eval {C} (e : ShallowSimpleTypedExpr (fun x => x) C) {struct e} : C := match e with
    | Const a => a
    | Var v => v
    | App A B H e1 e2 => ltac:(simpl in *; rewrite H in e1; exact ((eval _ e1) (eval _ e2)))
    | Abs A B H f => ltac:(simpl in *; inversion H; subst; intros x; exact (eval _ (f x)))
    end.


End Attempt4.

Include Attempt3.

End PHOASLam.
