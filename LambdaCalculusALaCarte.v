(* https://emilaxelsson.github.io/documents/axelsson2012generic.pdf *)

Inductive Spine : Type :=
    | Full : Type -> Spine
    | Partial : Type -> Spine -> Spine
    .

Fixpoint spineDenotation (x : Spine) : Type := match x with
    | Full a => a
    | Partial a b => a -> spineDenotation b
    end.

Fixpoint spineNonLast (x : Spine) : Type := match x with
    | Full a => unit
    | Partial a b => prod a (spineNonLast b)
    end.

Fixpoint spineLast (x : Spine) : Type := match x with
    | Full a => a
    | Partial a b => spineLast b
    end.

Fixpoint varUncurry (x : Spine) (f : spineDenotation x) (xs : spineNonLast x) {struct x} : spineLast x := ltac:(destruct x; [exact f | exact (varUncurry x (f (fst xs)) (snd xs))]).
Fixpoint varCurry (x : Spine) (f : spineNonLast x -> spineLast x) {struct x} : spineDenotation x := ltac:(destruct x; [exact (f tt) | exact (fun y => varCurry _ (fun z => f (y, z)))]).

Infix ":->" := Partial (at level 90, right associativity).

Inductive AST dom (sig : Spine) :=
    | Sym : dom sig -> AST dom sig
    | App : forall a, AST dom (a :-> sig) -> AST dom (Full a) -> AST dom sig
    .

Arguments Sym {_ _} _.
Arguments App {_ _ _} _ _.

Infix ":$" := App (at level 10).
Definition ASTF dom a := AST dom (Full a).

Inductive TyPlus (dom1 dom2 : Spine -> Type) a :=
    | InjL : dom1 a -> TyPlus dom1 dom2 a
    | InjR : dom2 a -> TyPlus dom1 dom2 a
    .

Arguments InjL {_ _ _} _.
Arguments InjR {_ _ _} _.

Infix ":+:" := TyPlus (at level 90, right associativity).

Class Subtype (sub sup : Spine -> Type) := {
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

Class BigStepEval (expr : Spine -> Type) := { big_step_eval : forall {a} (x : expr a), spineDenotation a }.

Instance BSE_TyPlus {sub1 sub2} `{_ : BigStepEval sub1} `{_ : BigStepEval sub2} : BigStepEval (sub1 :+: sub2) := {
        big_step_eval _ x := match x with InjL y => big_step_eval y | InjR y => big_step_eval y end
    }.

Instance BSE_AST {dom} `{_ : BigStepEval dom} : BigStepEval (AST dom) := {
    big_step_eval a x := (fix f a (x : AST dom a) := match x with
        | Sym y => big_step_eval y
        | App y z => (f _ y) (f _ z)
        end) a x
    }.

Inductive BooleanSym : Spine -> Type :=
    | BoolLit : bool -> BooleanSym (Full bool)
    | BoolUnop : (bool -> bool) -> BooleanSym (bool :-> Full bool)
    | BoolBinop : (bool -> bool -> bool) -> BooleanSym (bool :-> bool :-> Full bool)
    .

Instance BSE_BooleanSym : BigStepEval BooleanSym := {
    big_step_eval a (x : BooleanSym a) := match x with
        | BoolLit b => b
        | BoolUnop f => f
        | BoolBinop f => f
        end
    }.

Inductive IfExpr : Spine -> Type := IfThenElse : forall a, IfExpr (bool :-> a :-> a :-> Full a).
Instance BSE_IfExpr : BigStepEval IfExpr := { big_step_eval a x := match x with | IfThenElse _ => fun c t f => if c then t else f end }.

Definition not' {dom} `(_ : BooleanSym :<: dom) : ASTF dom bool -> ASTF dom bool := fun x => inj (BoolUnop negb) :$ x.

Definition demo_exp_1 : ASTF (IfExpr :+: BooleanSym) bool := inj (IfThenElse _) :$ (inj (BoolLit true)) :$ (inj (BoolLit false)) :$ (inj (BoolLit true)).

Inductive SimpLam V W : Spine -> Type :=
    | Var : forall {a}, V a -> SimpLam V W (Full a)
    | Abs : forall {a b}, (V a -> W b) -> SimpLam V W (a :-> b).
Definition SimpLam' W sig := forall V, SimpLam V W sig.

Instance BSE_SimpLam : BigStepEval (SimpLam' spineDenotation) := {
    big_step_eval s x := let x' := x (fun x => x) in
    match x' with Var _ _ y => y | Abs _ _ f => f end
    }.
Instance BSE_SimpLam' {dom} `{_ : BigStepEval dom} : BigStepEval (SimpLam' (AST dom)) := {
    big_step_eval _ x := let x' := x (fun x => x) in
    match x' with Var _ _ y => y | Abs _ _ f => fun y => big_step_eval (f y) end
    }.

Inductive NatSym : Spine -> Type := Zero : NatSym (Full nat) | Succ : NatSym (nat :-> Full nat).
Instance BSE_NatSym : BigStepEval NatSym := { big_step_eval _ x := match x with Zero => O | Succ => S end }.

Inductive PR dom : Spine -> Type := Rec : forall s, PR dom (AST dom s :-> AST dom (nat :-> spineLast s :-> s) :-> (nat :-> s)).
Instance BSE_PR dom `{_ : BigStepEval dom} : BigStepEval (PR dom) := {
    big_step_eval a x := match x in PR _ s return spineDenotation s with Rec _ s =>
        fun f g => fix h n := match n with
            | O => big_step_eval f
            | S n' => varCurry s (fun y => varUncurry s (big_step_eval g n' (varUncurry s (h n') y)) y)
        end
    end
    }.

Definition ast_fst {dom} {V} `{_ : SimpLam V (AST dom) :<: dom} {a b} : AST dom (a :-> b :-> Full a) := ltac:(apply Sym, inj, Abs; intro x; apply Sym, inj, Abs; intro y; apply Sym, inj, Var; exact x).
Fail Definition ast_fst' {dom} {V} `{_ : SimpLam V spineDenotation :<: dom} {a b} : AST dom (a :-> b :-> Full a) := ltac:(apply Sym, inj, Abs; exact (fun x y => x)). (* nonparametric *)

Inductive VoidSym : Spine -> Type := .

Fail Check (@App _ _ _ (Sym (Rec _ (nat :-> Full nat))) _).
Definition ast_plus  {V} : AST (PR VoidSym :+: (SimpLam V (AST VoidSym) :+: NatSym)) (nat :-> nat :-> Full nat).
refine (_ :$ _ :$ _).
- apply Sym; left.
    Fail apply Rec.
Abort.

Inductive hlist :=
    | hnil : hlist
    | hcons : forall A, A -> hlist -> hlist
    .

Inductive hElem {A} (x : A) : hlist -> Prop :=
    | hElemHead : forall xs, hElem x (hcons _ x xs)
    | hElemTail : forall {B} (y : B) xs, hElem x xs -> hElem x (hcons _ y xs)
    .

Class Search_hElem {A} (x : A) (xs : hlist) := { searchHlist : hElem x xs }.
Instance Search_hElem_Head {A} x xs : Search_hElem x (hcons A x xs) := ltac:(constructor; constructor).
Instance Search_hElem_Tail {A B} {y : B} (x : A) xs `{H : Search_hElem A x xs} : Search_hElem x (hcons B y xs) := ltac:(constructor; apply hElemTail; destruct H; assumption).

Inductive ContextedLam : hlist -> Spine -> Type :=
    | CtxVar : forall {A} (x : A) {xs}, hElem x xs -> ContextedLam xs (Full A)
    | CtxAbs : forall {A B xs}, (forall x, ContextedLam (hcons A x xs) (Full B)) -> ContextedLam xs (Full (A -> B))
    .

Instance BSE_ContextedLam (ctx : hlist) : BigStepEval (ContextedLam ctx) := ltac:(constructor; induction 1; assumption).

Inductive ContextedLam' dom : hlist -> Spine -> Type :=
    | CtxVar' : forall {A} (x : A) {xs}, hElem x xs -> ContextedLam' dom xs (Full A)
    | CtxAbs' : forall {A B xs}, (forall x, AST (dom :+: ContextedLam' dom (hcons A x xs)) (Full B)) -> ContextedLam' dom xs (Full (A -> B))
    .

Arguments CtxVar' {_ _} _ {_}.
Arguments CtxAbs' {_ _ _ _} _.

Fail Instance BSE_ContextedLam' {dom} `{_ : BigStepEval dom} (ctx : hlist) : BigStepEval (ContextedLam' dom ctx) := {
    big_step_eval spine :=
    (fix rec ctx' spine' (lam : ContextedLam' dom ctx' spine') {struct lam} : spineDenotation spine' :=
        match lam with
        | CtxVar' y _ => y
        | @CtxAbs' _ A B xs f => fun y => rec' _ _ (f y)
        end
    with rec' ctx' spine' (ast : AST (dom :+: ContextedLam' dom ctx') spine') {struct ast} : spineDenotation spine' :=
        match ast with
        | Sym (InjL z) => big_step_eval z
        | Sym (InjR z) => rec _ _ z (* Fails with `Recursive call to rec has principal argument equal to "z" instead of a subterm of "ast".` *)
        | App a b => (rec' _ _ a (rec' _ _ b))
        end
    for rec) ctx spine
    }.
(*Check @big_step_eval _ BSE_AST _ b.*)
(*Check Build_BigStepEval (AST (dom :+: ContextedLam' dom (hcons A y xs))) (fun s x => rec (hcons A y xs) _ _).*)

Definition embed_snd {dom} `{_ : ContextedLam hnil :<: dom} a b : AST dom (Full (a -> b -> b)) := inj (CtxAbs (fun _ => CtxAbs (fun y => CtxVar y searchHlist))).
Definition embed_snd' {dom} a b : AST (dom :+: ContextedLam' dom hnil) (Full (a -> b -> b)) := inj (CtxAbs' (fun _ => inj (CtxAbs' (fun y => inj (CtxVar' y searchHlist))))).

Compute big_step_eval (embed_snd nat nat).

Inductive PR' : Spine -> Type := Rec' : forall s, PR' (spineDenotation s :-> (nat -> spineLast s -> spineDenotation s) :-> Full (nat -> spineDenotation s)).
Instance BSE_PR' : BigStepEval PR' := {
    big_step_eval a x := _
    }.
(destruct x).
(induction s; simpl; intros).
- (induction H).
    + exact X.
    + exact (X0 H IHnat).
- refine (IHs (X X1) _ H).
    intros.
    exact (X0 H0 X2 X1).
Defined.

Definition PR_plus : AST (PR' :+: NatSym :+: ContextedLam hnil) (Full (nat -> nat -> nat)).
refine ((inj (Rec' (nat :-> Full nat)) : AST _ ((nat -> nat) :-> (nat -> nat -> nat -> nat) :-> Full (nat -> nat -> nat))) :$ _ :$ _).
- exact (inj (CtxAbs (fun x => CtxVar x searchHlist))).
- exact (inj (CtxAbs (fun x => CtxAbs (fun y => (CtxAbs (fun z => CtxVar x searchHlist)))))). (* this isn't yet correct, the shape of ContextedLam doesn't allow splicing in other domain elements, so we can't use Succ *)
Defined.
