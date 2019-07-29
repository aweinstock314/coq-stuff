(*
To build:
git clone https://github.com/FormalTheology/GoedelGod/ /tmp/GoedelGod
coqc -R /tmp/GoedelGod/Formalizations/Coq GoedelGod /tmp/GoedelGod/Formalizations/Coq/Modal.v
rlwrap coqtop -R /tmp/GoedelGod/Formalizations/Coq/ GoedelGod -l ModalAgents.v
*)

(* an attempt to port https://codereview.stackexchange.com/questions/225128/prisoners-dilemma-with-provability-logic to another embedding of modal logic *)
Require Import GoedelGod.Modal.

Theorem Pmodus : [mforall p, mforall q, box (p m-> q) m-> box p m-> box q ].
    intros w p q f x.
    box_i.
    box_e f f'.
    box_e x x'.
    exact (f' x').
Qed.
Definition Pmodus' : forall p q, [box (p m-> q) m-> box p m-> box q] := fun p q w x y => Pmodus w p q x y .

Theorem necessitation : forall p, [p] -> [box p].
Proof. intros p Hp w;  box_i; apply Hp. Qed.

Theorem inner_necessitation : [mforall p, box p m-> box (box p)].
- intros w p Hp; box_i; box_i; (box_e Hp Hp').
+ exact Hp'.
+ (apply (transitivity _ _ _ R R0)).
Qed.

(* https://plato.stanford.edu/entries/logic-provability/#CharModaSoun *)
Axiom conversely_wellfounded : forall (f : nat -> i), exists n, ~r (f n) (f (S n)).

 (* TODO: modal_fix should be provable from conversely_wellfounded *)
(*Axiom modal_fix : [mforall f, mexists p, p m<-> f (box p) ].*)
Axiom modal_fix : forall f, exists p, [p m<-> f (box p)].

(* https://en.wikipedia.org/wiki/Loeb's_theorem#Proof_of_L%C3%B6b's_theorem *)
Theorem loeb : [mforall p, box (box p m-> p) m-> box p].
(intros w p H).
destruct (modal_fix (fun phi => phi m-> p)) as [phi Hphi].
assert [box (phi m-> box phi m-> p)] as L4. {
 intros w1 w2 R0 X Y.
 destruct (Hphi w2) as [L R].
 exact (L X Y).
}
pose (L6 := Pmodus w (box phi) p).
