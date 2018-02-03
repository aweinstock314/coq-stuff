Scheme Equality for nat.

Definition dec_eq (A : Set) : Set := forall x y : A, {x = y} + {x <> y}.

Check nat_eq_dec : dec_eq nat.

Definition bool_eq_test (A : Set) (f : dec_eq A) (x y : A) : bool := sumbool_rec (fun _ => bool) (fun _ => true) (fun _ => false) (f x y).

Goal forall A f x y, bool_eq_test A f x y = true -> x = y.
    intros A f x y H.
    unfold dec_eq in f.
    compute in H.

(*
Unnamed_thm < Show.
1 subgoal

  A : Set
  f : forall x y : A, {x = y} + {x <> y}
  x, y : A
  H : (if f x y then true else false) = true
  ============================
  x = y
*)
(*
17:04:17 < aweinstock> unrelated question (about recovering information after branching on it to get a bool): in https://paste.rs/iBC, how can I find out what function the 'if/then/else' in H expands to? `Print Scopes.` only
                       gave me IF_then_else, which doesn't look like its type unifies
17:06:24 < aweinstock> (i.e. `Check fun (A : Set) (f : dec_eq A) (x y : A) => IF_then_else (f x y).` fails to typecheck)
17:09:25 < aweinstock> I tried `Unset Printing Notations.`, and it still shows up as `H : eq (if f x y then true else false) true`
17:13:53 < pgiarrusso> aweinstock: `if...then...else` is probably a primitive and has special behavior
17:14:06 < pgiarrusso> the condition can have any type with two constructors
17:14:14 < pgiarrusso> (IIRC)
17:14:16 < aweinstock> w.r.t. the dec_eq question, I found it in figure 1.1, and the behaviour in 2.2.2 (coq manual)
17:14:19 < pgiarrusso> no way to achieve that with a usual function
17:15:12 < aweinstock> the https://paste.rs/iBC thing is a minimal repro of an issue I ran into in a larger proof for the poset_lattice project (antisymmetry for a free-lattice construct)
17:17:43 < pgiarrusso> uh, `destruct f x y` should let you finish that proof
17:18:02 < pgiarrusso> (if you wonder about that)
17:19:37 < pgiarrusso> gotta leave (for now?), see you, hope the above helps!
17:20:46 < aweinstock> 'destruct f; [exact e | discriminate H]' solves the dec_eq thing, thanks!
*)

    destruct f as [e | ne]; [exact e | discriminate H].
    Qed.
