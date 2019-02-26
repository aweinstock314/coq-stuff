(* https://emilaxelsson.github.io/documents/axelsson2012generic.pdf *)

Inductive Full a := MkFull : a -> Full a.
Inductive Partial a b := MkPartial : (a -> b) -> Partial a b.

Infix ":->" := Partial (at level 90, right associativity).

Inductive AST dom sig :=
    | Sym : dom sig -> AST dom sig
    | App : forall a, AST dom (a  :-> sig) -> AST dom (Full a) -> AST dom sig
    .

Arguments Sym {_ _} _.
Arguments App {_ _ _} _ _.

Infix ":$" := App (at level 10).
Definition ASTF dom a := AST dom (Full a).

Inductive TyPlus (dom1 dom2 : Type -> Type) a :=
    | InjL : dom1 a -> TyPlus dom1 dom2 a
    | InjR : dom2 a -> TyPlus dom1 dom2 a
    .

Arguments InjL {_ _ _} _.
Arguments InjR {_ _ _} _.

Infix ":+:" := TyPlus (at level 90).

Class Subtype (sub sup : Type -> Type) := {
    inj : forall a, sub a -> sup a;
    prj : forall a, sup a -> option (sub a);
    }.

Arguments inj {_ _ _ _} _.
Arguments prj {_ _ _ _} _.

Infix ":<:" := Subtype (at level 90).

Instance IdentitySubtype : forall exp, exp :<: exp := {
    inj := fun _ x => x;
    prj := fun _ x => Some x;
    }.

Instance PlusSubtypeL sym dom : sym :<: (sym :+: dom) := {
    inj := fun _ x => InjL x;
    prj := fun _ x => match x with InjL y => Some y | _ => None end;
    }.

Instance PlusSubtypeR sym1 sym2 dom `(_ : sym1 :<: dom) : sym1 :<: (sym2 :+: dom) := {
    inj := fun _ x => InjR (inj x);
    prj := fun _ x => match x with InjR y => prj y | _ => None end;
    }.

Instance ASTSubtype sub sup `(_ : sub :<: sup) : sub :<: AST sup := {
    inj := fun _ x => Sym (inj x);
    prj := fun _ x => match x with Sym y => prj y | _ => None end;
    }.

Class Denotation (sig : Type) := { un_denotation : Type }.
Instance FullDenotation a : Denotation (Full a) := { un_denotation := a }.
Instance PartialDenotation a b `(_ : Denotation b) : Denotation (Partial a b) := { un_denotation := a -> un_denotation }.

Definition denotation (a : Type) `{_ : Denotation a} := un_denotation.

Class BigStepEval (expr : Type -> Type) := { big_step_eval : forall a `(_ : Denotation a), expr a -> denotation a }.

Inductive BooleanSym : Type -> Type :=
    | BoolLit : bool -> BooleanSym (Full bool)
    | BoolUnop : (bool -> bool) -> BooleanSym (bool :-> Full bool)
    | BoolBinop : (bool -> bool -> bool) -> BooleanSym (bool :-> bool :-> Full bool)
    .

Set Printing Implicit.

Fail Instance BSE_BooleanSym : BigStepEval BooleanSym := {
    big_step_eval a _ (x : BooleanSym a) := match x with
        | BoolLit b => b
        | BoolUnop f => f
        | BoolBinop f => f
        end
    }.

Inductive IfExpr : Type -> Type := IfThenElse : forall a, IfExpr (bool :-> a :-> a :-> Full a).

Definition not' {dom} `(_ : BooleanSym :<: dom) : ASTF dom bool -> ASTF dom bool := fun x => inj (BoolUnop negb) :$ x.

Definition demo_exp_1 : ASTF (IfExpr :+: BooleanSym) bool := inj (IfThenElse _) :$ (inj (BoolLit true)) :$ (inj (BoolLit false)) :$ (inj (BoolLit true)).
