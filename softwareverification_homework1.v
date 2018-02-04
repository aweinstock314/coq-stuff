(*
This defines the exp function by recursion on peano naturals. The "Fixpoint" keyword 
is required for recursive definitions (instead of "Definition"), and the recursive 
calls must make one argument structurally smaller in order for termination to be 
automatically verified (which is needed for logical soundness).
*)
Fixpoint exp (b e : nat) : nat :=
    match e with
    | 0 => 1
    | S e' => b * exp b e'
    end.

(*
These are two scripts for "Ltac", Coq's proof automation language, that are 
enough to prove anything that's provable by a combination of 1 step of beta 
reduction and induction. This includes most properties of addition, and some 
properties of multiplication. Hooks for more complex logic are provided by the 
first script, which shortens some later proofs. The "[ a | b ]; c" syntax is used 
to run a in the first case (of a proof by cases/induction), b in the second case, 
and c afterwards.
*)
Ltac simple_nat_induction n c1 c2 := intros; induction n as [ | n IHn ]; simpl; [ c1 | rewrite IHn; c2 ]; reflexivity.
Ltac simple_nat_induction' n := simple_nat_induction n idtac idtac.

(* Right reduction properties for plus (the standard library defines it left-recursively) *)
Theorem plus_rightzero : forall n, n + 0 = n. simple_nat_induction' n. Qed.
Theorem plus_rightsucc : forall n m, n + (S m) = S (n + m). simple_nat_induction' n. Qed.

(* Associativity/commutativity for plus are fairly routine; "ltac:(...)" is used to pass ltac script fragments as arguments *)
Theorem plus_associative : forall x y z, (x + y) + z = x + (y + z). simple_nat_induction' x. Qed.
Theorem plus_commutative : forall n m, n + m = m + n. simple_nat_induction n ltac:(rewrite plus_rightzero) ltac:(rewrite plus_rightsucc). Qed.

(* Right reduction properties for mult (the standard library defines it left-recursively) *)
Theorem mult_rightzero : forall n, n * 0 = 0. simple_nat_induction' n. Qed.
Theorem mult_rightsucc : forall n m, n * (S m) = (n * m) + n. simple_nat_induction n idtac ltac:(rewrite plus_rightsucc, plus_associative). Qed.

(*
The proof of associativity of multiplication is more involved than the 
corresponding proof for addition, and requires the distributivity of 
multiplication as a lemma. The distributivity proofs basically involve 
shuffling terms around with addition's properties in the inductive step.
*)
Theorem mult_leftdist : forall x y z, x * (y + z) = x * y + x * z.
    intros; induction x.
    - reflexivity.
    - simpl. rewrite IHx.
        rewrite (plus_associative y (x * y) (z + x * z)).
        rewrite <- (plus_associative (x * y) z (x * z)).
        rewrite (plus_commutative (x * y) z).
        (* "repeat rewrite" is used here to turn the expression tree back into a linked 
        list after the rewrites have been done (association can be thought of as tree 
        rotation, and commutation as swapping left and right subtrees *)
        repeat rewrite <- plus_associative.
        reflexivity.
    Qed.
(* in the right-distributive case, "repeat rewrite" is used to apply right reductions until they no longer apply *)
Theorem mult_rightdist : forall x y z, (x + y) * z = x * z + y * z.
    intros; induction z.
    - repeat rewrite mult_rightzero. reflexivity.
    - repeat rewrite mult_rightsucc. rewrite IHz.
        rewrite (plus_commutative (y * z) y).
        rewrite (plus_associative (x * z) x (y + y * z)).
        rewrite <- (plus_associative x y (y * z)).
        rewrite (plus_commutative (x + y) (y * z)).
        rewrite plus_associative.
        reflexivity.
    Qed.

(* Associativity/commutativity for mult are straightforward once the above lemmas have been proven *)
Theorem mult_associative : forall x y z, (x * y) * z = x * (y * z).
    intros; induction x; [| simpl; rewrite mult_rightdist, IHx ]; reflexivity.
    Qed.

Theorem mult_commutative : forall n m, n * m = m * n.
    intros n m; induction n; simpl;
        [ rewrite mult_rightzero
        | rewrite mult_rightsucc, (plus_commutative m (n * m)), IHn
    ]; reflexivity.
    Qed.

(*
The original goal of part 1 (that exponentiation distributes over multiplication) 
involves term rewriting using multiplication's associativity / commutatitivity, 
which all of the above was building up to. The first one was written purely 
interactively, the second one was written with the benefit of hindsight and 
includes the intermediate contexts to make the rewrites visible in the source.
*)
Theorem exp_dist : forall n x y, exp (x*y) n = exp x n * exp y n.
    intros n x y. induction n.
    - reflexivity.
    - simpl.
        rewrite (mult_associative x (exp x n) (y * exp y n)).
        rewrite <- (mult_associative (exp x n) y (exp y n)).
        rewrite (mult_commutative (exp x n) y).
        rewrite IHn.
        repeat rewrite mult_associative.
        reflexivity.
    Qed.

Theorem exp_dist' : forall n x y, exp (x*y) n = exp x n * exp y n.
    intros n x y. induction n as [| n IHn].
    - reflexivity.
    - simpl. repeat match goal with
    | |- (x * y) * exp (x * y) n = (x * exp x n) * (y * exp y n) => rewrite (mult_associative x (exp x n) (y * exp y n))
    | |- (x * y) * exp (x * y) n = x * (exp x n * (y * exp y n)) => rewrite <- (mult_associative (exp x n) y (exp y n))
    | |- (x * y) * exp (x * y) n = x * ((exp x n * y) * exp y n) => rewrite (mult_commutative (exp x n) y)
    | |- (x * y) * exp (x * y) n = x * ((y * exp x n) * exp y n) => rewrite IHn
    | |- (x * y) * (exp x n * exp y n) = x * ((y * exp x n) * exp y n) => repeat rewrite mult_associative
    end. reflexivity.
    Qed.

(*
The third proof of distributivity (exp_dist'') makes use of Coq's library for 
reasoning about algebraic [semi-]rings. It handles associative/commutative 
rewrites by abstracting terms into variables in a polynomial and putting the 
polynomial into canonical form. This results in an extremely short/robust 
proof. The bulk of the work of proving that Peano naturals form a semiring is 
{associativity,commutativity} of {addition,multiplication}; the remainder is 
straightforward reductions involving 0/1.
*)

Require Export Ring.
Definition nat_semiring : Ring_theory.semi_ring_theory 0 1 plus mult eq := {|
    SRadd_0_l := fun _ => eq_refl;
    SRadd_comm := plus_commutative;
    SRadd_assoc := (fun x y z => eq_sym (@ plus_associative x y z));
    SRmul_1_l := fun x => ltac:(simpl; rewrite plus_rightzero; reflexivity) : 1 * x = x;
    SRmul_0_l := fun _ => eq_refl;
    SRmul_comm := mult_commutative;
    SRmul_assoc := (fun x y z => eq_sym (@ mult_associative x y z));
    SRdistr_l := mult_rightdist;
    |}.
Add Ring nat_semiring : nat_semiring.
Theorem exp_dist'' : forall n x y, exp (x*y) n = exp x n * exp y n.
    intros n x y; induction n as [| n IHn]; simpl; [| rewrite IHn; ring_simplify ]; reflexivity.
    Qed.

(*
For part 2, I did each proof both with explicit term manipulation, and then 
with ltac (under the same name suffixed with a prime). The term manipulation 
proofs are longer in the source, but the ltac proofs expand into longer terms.

According to the Coq manual, "tauto" implements a decision procedure for 
tautologies in intuitionistic logic from a 1992 paper in the Journal of Symbolic 
Logic. It's sufficient to completely solve 4.4 a on it's own, and sufficient to 
solve 4.4 b once the Law of the Excluded Middle has been brought into scope.
*)

(* 4.4 a is basically currying, with (conj/proj1/proj2) in Prop instead of (pair/fst/snd) in Set *)
Definition part2_44_a : forall (A B C : Prop), (A -> B -> C) -> (A /\ B -> C) := fun A B C f x => f (proj1 x) (proj2 x).
Theorem part2_44_a' : forall (A B C : Prop), (A -> B -> C) -> (A /\ B -> C). tauto. Qed.

(* 4.4 b requires the Law of the Excluded Middle, which isn't a primitive in the Calculus of Constructions, and must be asserted as an axiom. *)
Axiom LEM : forall P, P \/ ~P.
(*
The "match ... with ... end" construct is used for pattern matching at the value level 
(i.e. in kind Set), and proof by cases at the proof level (i.e. in kind Prop). Proof by 
contradiction in CoC ends up being a special case of proof by cases, with the False type 
(representing a contradiction) having 0 constructors, and a disjunction with 0 cases not 
requiring any steps to prove the conclusion. ~E is sugar for (E -> False), so that if E 
is instantiated, the term of type ~E can be applied to it get a value of type False, 
which can be pattern matched on to get the principle of explosion.

The "fun ... => ..." construct is used for lambdas, which are typed as either 
implications or foralls (necessarily as the latter if the type of the body 
depends on the value of the binder, i.e. a dependent type)
*)
Definition part2_44_b : forall (A B C D E : Prop), (A \/ B -> C \/ D -> E) -> (A -> ~E -> ~C) :=
    fun A B C D E f a ne => match LEM C with
    | or_introl c => match (ne (f (or_introl a) (or_introl c))) with end
    | or_intror nc => nc
    end.
Theorem part2_44_b' : forall (A B C D E : Prop), (A \/ B -> C \/ D -> E) -> (A -> ~E -> ~C).
    intros; destruct (LEM C); tauto.
    Qed.
