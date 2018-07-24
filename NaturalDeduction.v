Require Import List.
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

Inductive Derivation : list AST -> AST -> Prop :=
    | BotElim : forall phi, Derivation [Bot] phi
    | NegElim : forall phi, Derivation [phi; Neg phi] Bot
    | NegIntro : forall gamma phi, Derivation (cons phi gamma) Bot -> Derivation gamma (Neg phi)
    | AndIntro : forall phi psi, Derivation [phi; psi] (And phi psi)
    | AndElimL : forall phi psi, Derivation [And phi psi] phi
    | AndElimR : forall phi psi, Derivation [And phi psi] psi
    | ImpElim : forall phi psi, Derivation [phi; Imp phi psi] psi
    | ImpIntro : forall gamma phi psi, Derivation (cons phi gamma) psi -> Derivation gamma (Imp phi psi)
    | OrIntroL : forall phi psi, Derivation [phi] (Or phi psi)
    | OrIntroR : forall phi psi, Derivation [psi] (Or phi psi)
    | OrElim : forall gamma delta psi phi chi, Derivation (cons psi gamma) chi -> Derivation (cons phi delta) chi -> Derivation ([Or phi psi]++gamma++delta) chi
    .

Example derive_true : Derivation [] (Neg Bot).
Proof. repeat constructor. Defined.

Theorem soundness : ~Derivation [] Bot.
Proof. inversion 1. Defined.
End IPL.
