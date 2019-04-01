Definition uncountable (A : Type) := ~(exists (f : nat -> A), forall (x : A), exists n, f n = x).
Definition infiniteBitVec := nat -> bool.

Theorem uncountable_infiniteBitVec : uncountable infiniteBitVec.
intros [f H].
destruct (H (fun i => negb (f i i))).
destruct (f x x) eqn:H'; (pose (e := f_equal (fun g => g x) H0); simpl in e; rewrite H' in e; discriminate).
Qed.
