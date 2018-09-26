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

Module TypeSystem1.
Record TypeSystem := {
    T : Type -> Type; (* typing derivations, indexed over the type of constants *)
    Inj : forall A, T A; (* injecting a constant *)
    Arr : Type -> Type -> {C & T C}; (* the arrow constructor *)
    (*Inj_comm_Arr : forall A B, Inj (projT1 (Arr A B)) = projT2 (Arr A B);*)
    }.

(* notes from shellphish party:
suggested modification: Record TypeSystem := { T : Type; Arr : T -> T -> T; interp : T -> Type }
Const for A should require T s.t. interp T = A
TODO: look into kami? (doesn't have arbitrary typing derivations, but for familiarity with PHOAS
"cross crypto" in MIT-PLV GH organisation
cross crypto depends on FCF, extends it in some way? lemmas/tactics for use with FCF?
*)

Definition ShallowSimpleType := {|
    T := fun _ => Type;
    Inj := fun x => x;
    Arr := fun a b => existT _ (a -> b) (a -> b);
    (*Inj_comm_Arr := ltac:(simpl in *; intros; reflexivity);*)
    |}.

Definition Untyped := {|
    T := fun _ => unit;
    Inj := fun _ => tt;
    Arr := fun unit unit => existT _ unit tt;
    (*Inj_comm_Arr := ltac:(simpl in *; intros; reflexivity);*)
    |}.
End TypeSystem1.

Module Attempt3.
Include TypeSystem1.
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
Include TypeSystem1.

Ltac with_sigT x := match goal with
    (*| e : _ = projT1 x |- _ => let H := fresh in set (H := projT2 x); rewrite <- e in H; exact H*)
    | e : _ = projT1 x |- _ => exact (eq_rect_r _ (projT2 x) e)
    (*| e : _ = projT1 x |- _ => exact (eq_rect (projT1 x) (fun y => _ y) (projT2 x) _ (eq_sym e))*)
    (*| e : _ = projT1 x |- _ => exact (match eq_sym e in (_ = y) return (_ y) with eq_refl => projT2 x end)*)
    end.
Inductive Expr (TS : TypeSystem) (V : Type -> Type) (C : Type) : T TS C -> Type :=
    | Const : C -> Expr TS V C (Inj TS C)
    | Var : V C -> Expr TS V C (Inj TS C)
    | App : forall A, Expr TS V (projT1 (Arr TS A C)) (projT2 (Arr TS A C)) -> Expr TS V A (Inj TS A) -> Expr TS V C (Inj TS C)
    | Abs : forall A B (e : C = projT1 (Arr TS A B)), (V A -> Expr TS V B (Inj TS B)) -> Expr TS V C ltac:(with_sigT (Arr TS A B)).

Definition const {TS} {V} {A} (x : A) : Expr TS V A (Inj TS A) := Const TS V A x.
Definition var {TS} {V} {A} (x : V A) : Expr TS V A (Inj TS A) := Var TS V A x.
Definition app {TS} {V} {A B} (e1 : Expr TS V (projT1 (Arr TS A B)) _) e2 : Expr TS V B (Inj TS B) := App TS V B A e1 e2.
Definition abs {TS} {V} {A B C} {H : C = projT1 (Arr TS A B)} (x : V A -> Expr TS V _ (Inj TS B)) : Expr TS V _ ltac:(with_sigT (Arr TS A B)) := Abs TS V C A B H x.

Definition embed_id' {TS} {V} {A C} {H : C = projT1 (Arr TS A A)} : Expr TS V C ltac:(with_sigT (Arr TS A A)) := abs (fun x => var x).
Definition embed_id {TS} {V} {A} : Expr TS V (projT1 (Arr TS A A)) (projT2 (Arr TS A A)) := @embed_id' TS V _ _ eq_refl.

Definition ShallowSimpleTypedExpr (V : Type -> Type) (A : Type) : Type := Expr ShallowSimpleType V A A.

Fixpoint eval {C} (e : ShallowSimpleTypedExpr (fun x => x) C) {struct e} : C := match e with
    | Const a => a
    | Var v => v
    | App A e1 e2 => (eval e1) (eval e2)
    | Abs A B H f => ltac:(simpl in *; rewrite H; intros x; exact (eval _ (f x)))
    end.

Definition UntypedExpr (V : Type -> Type) := Expr Untyped V unit tt.

Definition uapp {V} (e1 e2 : UntypedExpr V) : UntypedExpr V := app e1 e2.
Definition uabs {V : Type -> Type} (e1 : V unit -> UntypedExpr V) : UntypedExpr V := Abs Untyped V unit unit unit eq_refl e1.

Definition selfapply {V} : UntypedExpr V := uabs (fun x => uapp (var x) (var x)).
Definition diverge {V} : UntypedExpr V := uapp selfapply selfapply.

Definition betaOpt {TS} {B} {U V : Type -> Type} (e : forall U, Expr TS U B (Inj TS B)) : option (Expr TS V B (Inj TS B)).
    (*refine (match e (fun _ => Expr _ _ (forall W, W) _) with*)
    refine (match e U with
    | App A (Abs a b H E1) E2 => Some _
    | _ => None
    end).
    (*assert (A = a /\ B = b). {
        clear E1 E2 e0 e.
    *)
    Abort.
Definition betaOpt {V : Type -> Type} (e : forall U, UntypedExpr U) : option (UntypedExpr V).
    refine (match e _ with
    | App A (Abs a b H E1) E2 => Some _
    | _ => None
    end).
    simpl in *. subst. simpl in *. apply E1.
    Abort.
End Attempt4.


Module TypeSystem2.

Record TypeSystem := {
    T : Type;
    Arr : Type -> Type -> Type;
    interp : T -> Type;
    }.

Definition ShallowSimpleType := {|
    T := Type;
    Arr := fun a b => (a -> b);
    interp := fun x => x
    |}.
Definition Untyped := {|
    T := unit;
    Arr := fun _ _ => unit;
    interp := fun _ => unit;
    |}.
End TypeSystem2.

Module Attempt5.
Include TypeSystem2.
Inductive Expr (TS : TypeSystem) (V : Type -> Type) : Type -> Type :=
    | Const : forall A, A -> Expr TS V A
    | Var : forall A, V A -> Expr TS V A
    | App : forall A B, Expr TS V (Arr TS A B) -> Expr TS V A -> Expr TS V B
    | Abs : forall A B, (V A -> Expr TS V B) -> Expr TS V (Arr TS A B).

Definition embed_id {TS} {V} {A} : Expr TS V (Arr _ A A) := Abs _ _ _ _ (fun x => Var _ _ _ x).

Definition uapp {V} (e1 e2 : Expr Untyped V unit) : Expr Untyped V unit := App _ V unit unit e1 e2.

Definition selfapply {V} : Expr Untyped V unit := Abs _ _ _ _ (fun x => uapp (Var _ _ _ x) (Var _ _ _ x)).
Definition diverge {V} : Expr Untyped V unit := uapp selfapply selfapply.

Fixpoint eval {A} (e : Expr ShallowSimpleType (fun x => x) A) : A := match e with
    | Const _ x => x
    | Var _ x => x
    | App _ _ e1 e2 => (eval e1) (eval e2)
    | Abs _ _ f => fun x => eval (f x)
    end.

Inductive BetaStep {TS} {V} {A} (f : Expr TS V A -> V A) : Expr TS V A -> Expr TS V A -> Prop :=
    | EAppAbs : forall context e1 e2, BetaStep f (context (App _ _ _ _ (Abs _ _ A A e1) e2)) (context (e1 (f e2)))
    | EVar : forall context e1, BetaStep f (context (Var _ _ _ (f e1))) (context e1).

Inductive KleenePlus A (R : A -> A -> Prop) : A -> A -> Prop :=
    | KPSing : forall x y, R x y -> KleenePlus A R x y
    | KPCons : forall x y z, R x y -> KleenePlus A R y z -> KleenePlus A R x z.

(* KP_eq is just a sanity check that KleenePlus is defined correctly *)
Lemma KP_eq : forall A x y, KleenePlus A eq x y <-> x = y.
Proof. intros A x y; split; intros H; [induction H | constructor]; congruence. Qed.

Definition BetaPlus {TS} {V} {A} f := KleenePlus _ (@BetaStep TS V A f).

Theorem diverge_diverges : forall V f, @BetaPlus Untyped V unit f diverge diverge.
intros.
eapply KPCons.
    unfold diverge; eapply (EAppAbs f (fun x => x)).
eapply KPCons.
    eapply (EVar f _).
eapply KPSing.
    apply (EVar f (fun x => uapp x selfapply)).
Qed.

End Attempt5.

Include Attempt5.

End PHOASLam.
