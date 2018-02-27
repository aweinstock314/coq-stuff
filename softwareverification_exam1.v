(*
A transcript of the proof states can be obtained with the following bash command (71 was obtained via binary search):
(echo 'Set Ltac Debug. Load "softwareverification_exam1.v".' && (yes 's' | head -n 71)) | coqtop > softwareverification_exam1_transcript.txt
*)

(*
The proof I had initially written on paper for question 1 had a type that failed typecheck:
forall (Object : Type) (P Q : Object -> Prop), { x | P x \/ Q x } <-> ({x | P x} \/ {x | Q x})

This fails for a rather subtle reason: Coq has 3 different representations of existential types:
Excerpt from "Print Scopes.":
"{ x  |  P }" := sig (fun x => P)
"{ x : A  & P }" := sigT (fun x => P)
"'exists' x .. y , p" := ex (fun y => .. (ex (fun y => p)) ..)
Output of several "Print"s after "Unset Printing Notations":
Inductive sig (A : Type) (P : forall _ : A, Prop) : Type :=
    exist : forall (x : A) (_ : P x), sig P
Inductive sigT (A : Type) (P : forall _ : A, Type) : Type :=
    existT : forall (x : A) (_ : P x), sigT P
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
    ex_intro : forall (x : A) (_ : P x), ex P

Coq has three "universes" for types: Set, Prop, and Type. Set and Prop are disjoint.
- Set is the type of data/functions which should be extracted to code.
- Prop is for logical statements that can be guarenteed to be erased at compile time.
- Set and Prop are both subtypes of Type, which is used for properties that involve a mix of things that can and can't be guarenteed to be erased.

The three existential types make use of these in different ways:
- all three are quantified over the universe (A : Type) of their witness (x : A), allowing x to be in Set, Prop, or Type
- sig's statement is of type Prop, but the result is in Type.
- sigT's statement is of type Type, and the result is in Type.
- ex's statement is of type Prop, and the result is in Prop.

I had initially used sig, whose result is in Type, which renders it incompatible with or (written "\/") which is of type (Prop -> Prop -> Prop).

I then tried to fix it by defining an analogue of iff (iffT) in Type, and changing uses of and/or with prod/sum, resulting in the following type q1goal:
iffT { x : Object & sum (P x) (Q x) } (sum { x | P x } { x | Q x })

This works (with no changes to the written proof), but is inelegant (in my view) because it requires the stronger sigT in the LHS (for the use of sum) and it is no longer able to use the built in infix operators.

Fortunately, while writing this up, I found out that "ex" is in the standard library (via the aforementioned "Print Scopes" introspection command of Coq), and was able to change the type of q1goal to:
(exists x, P x \/ Q x) <-> ((exists x, P x) \/ (exists x, Q x)).

Which typechecks with exactly the same proof, and lives entirely in Prop (i.e. the smallest possible universe for proofs).
*)
Definition iffT (P : Type) (Q : Type) : Type := prod (P -> Q) (Q -> P).

Section Question1.
    Theorem q1goal : forall (Object : Type) (P Q : Object -> Prop),
        (exists x, P x \/ Q x) <-> ((exists x, P x) \/ (exists x, Q x)).
        intros Object P Q. split.
        - (* LHS -> RHS *)
            intro H. destruct H as [x PQ].
            destruct PQ as [Px | Qx].
            + left. exists x. exact Px.
            + right. exists x. exact Qx.
        - (* RHS -> LHS *)
            intro H. destruct H as [eP | eQ].
            + destruct eP as [x Px]. exists x. left. exact Px.
            + destruct eQ as [x Qx]. exists x. right. exact Qx.
        Qed.
    Theorem q1goal_shortproof : forall (Object : Type) (P Q : Object -> Prop),
        (exists x, P x \/ Q x) <-> ((exists x, P x) \/ (exists x, Q x)).
        intros Object P Q. split; intro H.
        - (* LHS -> RHS *)
            destruct H as [x [PQ | PQ]]; [left | right]; exists x; exact PQ.
        - (* RHS -> LHS *)
            destruct H as [[x PQ] | [x PQ]]; exists x; [left | right]; exact PQ.
        Qed.
End Question1.

Section Question2.
    Parameter Object : Type.
    Parameter P Q : Object -> Prop.
    Parameter R : Object -> Object -> Prop.

    Definition P1 := { x | P x }.
    Definition P2 := { x | Q x }.
    Definition P3 := forall x, P x -> forall y, Q y -> R x y.

    Theorem q2goal : P1 -> P2 -> P3 -> exists xy, R (fst xy) (snd xy).
        intros eP eQ prop3.
        destruct eP as [x Px], eQ as [y Qy].
        exists (x, y).
        exact (prop3 x Px y Qy).
        Qed.

    Theorem q2goal_curried : P1 -> P2 -> P3 -> exists x y, R x y.
        intros eP eQ prop3.
        destruct eP as [x Px], eQ as [y Qy].
        exists x, y.
        exact (prop3 x Px y Qy).
        Qed.
End Question2.
