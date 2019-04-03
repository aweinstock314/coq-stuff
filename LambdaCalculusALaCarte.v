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

Inductive ContextedLam'' dom : nat -> hlist -> Spine -> Type :=
    | CtxVar'' : forall {n} {A} (x : A) {xs}, hElem x xs -> ContextedLam'' dom n xs (Full A)
    | CtxAbs'' : forall {n A B xs}, (forall x, AST (dom :+: ContextedLam'' dom n (hcons A x xs)) (Full B)) -> ContextedLam'' dom (S n) xs (Full (A -> B))
    .

Arguments CtxVar'' {_ _ _} _ {_}.
Arguments CtxAbs'' {_ _ _ _ _} _.

Definition lam_ast_rect_mut
    (Pdom : forall dom spine, dom spine -> Type)
    (Past : forall dom spine, AST dom spine -> Type)
    (HSym : forall dom spine (x : dom spine), Pdom _ _ x -> Past _ _ (Sym x))
    (Hinl : forall domL domR spine (x : domL spine), Pdom domL spine x -> Pdom (domL :+: domR) spine (InjL x))
    (Hinr : forall domL domR spine (x : domR spine), Pdom domR spine x -> Pdom (domL :+: domR) spine (InjR x))
    (HApp : forall dom a spine (x : AST dom (a :-> spine)) (y : AST dom (Full a)), Past _ _ x -> Past _ _ y  -> Past _ _ (App x y))
    (HVar : forall dom A (x : A) xs (wit : hElem x xs), Pdom (ContextedLam' dom _) (Full A) (CtxVar' x wit))
    (HLam : forall dom A B ctx (f : forall x, AST (dom :+: ContextedLam' dom (hcons A x ctx)) (Full B)), (forall x, Past _ _ (f x)) -> Pdom (ContextedLam' dom ctx) (Full (A -> B)) (CtxAbs' f))
    dom ctx spine (lam : ContextedLam' dom ctx spine)
    (Hdom : forall spine (x : dom spine), Pdom dom spine x)
    : Pdom (ContextedLam' dom ctx) spine lam
:= ((fix recLam dom' (Hdom' : forall spine'' (x : dom' spine''), Pdom _ _ x) ctx' spine' lam { struct lam } : Pdom (ContextedLam' dom' ctx') spine' lam :=
    match lam with
    | @CtxVar' _ A x xs y => HVar dom' A x xs y
    | @CtxAbs' _ A B xs f => HLam dom' A B xs f (fun x =>
        (fix recAst dom' (Hdom' : forall spine'' (x : dom' spine''), Pdom _ _ x) ctx' spine' ast { struct ast } : Past (dom' :+: ContextedLam' dom' ctx') spine' ast :=
            match ast as ast' return Past _ _ ast' with
            | Sym x => HSym _ _ _ (match x as x' return Pdom _ _ x' with
                | InjL y => Hinl _ _ _ _ (Hdom' _ _)
                | InjR y => Hinr _ _ _ _ (recLam _ (fun _ _ => Hdom' _ _) _ _ y)
                end)
            | App x y => HApp _ _ _ x y (recAst _ (fun _ _ => Hdom' _ _) _ _ x) (recAst _ (fun _ _ => Hdom' _ _) _ _ y)
            end) _ (fun _ _ => Hdom' _ _) _ _ (f x)
        )
    end
    ) dom Hdom ctx spine lam).

Instance BSE_ContextedLam' {dom} `{_ : BigStepEval dom} (ctx : hlist) : BigStepEval (ContextedLam' dom ctx) := {
    big_step_eval spine lam := lam_ast_rect_mut
        (fun _ s _ => spineDenotation s) (fun _ s _ => spineDenotation s)
        (fun _ _ _ x => x) (fun _ _ _ _ x => x) (fun _ _ _ _ x => x) (fun _ _ _ _ _ f x => f x) (fun _ _ x _ _ => x)
        (fun _ _ _ _ _ f => f) _ _ _ lam (fun _ x => big_step_eval x)
    }.

Definition var {dom dom' A xs} (x : A) `{_ : Search_hElem A x xs} `{_ : Subtype (ContextedLam' dom xs) dom'} : ASTF dom' A := inj (CtxVar' x searchHlist).
Definition abs {dom dom' A B xs} `{_ : Subtype (ContextedLam' dom xs) dom'} (f : forall x, ASTF (dom :+: ContextedLam' dom (hcons A x xs)) B) : ASTF dom' (A -> B) := inj (CtxAbs' f).

Definition embed_snd {dom} `{_ : ContextedLam hnil :<: dom} a b : AST dom (Full (a -> b -> b)) := inj (CtxAbs (fun _ => CtxAbs (fun y => CtxVar y searchHlist))).
Definition embed_snd' {dom} a b : AST (dom :+: ContextedLam' dom hnil) (Full (a -> b -> b)) := abs (fun _ => abs (fun y => var y)).
Definition embed_snd'' {dom} a b : AST (dom :+: ContextedLam'' dom 2 hnil) (Full (a -> b -> b)) := inj (CtxAbs'' (fun _ => inj (CtxAbs'' (fun y => inj (CtxVar'' y searchHlist))))).

Compute big_step_eval (embed_snd nat nat).
Compute big_step_eval (embed_snd' nat nat).

Inductive PR' : Spine -> Type := Rec' : forall s, PR' (spineDenotation s :-> (nat -> spineLast s -> spineDenotation s) :-> Full (nat -> spineDenotation s)).
Instance BSE_PR' : BigStepEval PR' := {
    big_step_eval a x := match x with
        Rec' s => fun f g => fix h (n : nat) := match n with
            | O => f
            | S n' => varCurry _ (fun xs => varUncurry _ (g n' (varUncurry _ (h n') xs)) xs)
            end
        end
    }.

Definition PR_plus : AST (PR' :+: NatSym :+: ContextedLam' NatSym hnil) (Full (nat -> nat -> nat)).
refine ((inj (Rec' (nat :-> Full nat)) : AST _ ((nat -> nat) :-> (nat -> nat -> nat -> nat) :-> Full (nat -> nat -> nat))) :$ _ :$ _).
- exact (abs (fun x => var x)).
- exact (abs (fun x => abs (fun y => abs (fun z => Sym (inj Succ) :$ (var y))))).
Defined.

Lemma PR_plus_compat_plus : forall x y, big_step_eval PR_plus x y = x + y.
intros x y; induction x.
- reflexivity.
- simpl in *; rewrite IHx; reflexivity.
Qed.

Example ContextedLam'_exotic_term : big_step_eval (abs (fun x => abs (fun y => abs (fun z => match x with true => var y | false => var z end))) : ASTF (ContextedLam' NatSym hnil) (bool -> nat -> nat -> nat)) true 5 42 = 5. reflexivity. Qed.
