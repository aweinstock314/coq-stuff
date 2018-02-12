(* This is a minimized example of an issue that came up when trying to prove https://github.com/aweinstock314/coq-stuff/blob/22fb223a5b278559f4ca49e041fa285cecdf3755/poset_lattice.v#L42-L68 *)
Inductive dec_eq {A : Type} {x y : A} := 
      Eq : (x=y) -> dec_eq
    | Neq : (x <> y) -> dec_eq.

Record foo : Type := mkFoo {
    t : Type;
    f : t -> t -> bool;
    }.

Record bar : Type := mkBar {
    t' : Type;
    f' : forall (x y : t'), @dec_eq t' x y;
    }.

Definition convert (b : bar) : foo := {| t := t' b; f := fun x y => match f' b x y with Eq _ => true | Neq _ => false end |}.

Theorem trans (b : bar) : forall x y z, f (convert b) x y = true /\ f (convert b) y z = true -> f (convert b) x z = true.
    intros x y z; simpl.
    set (fxy := f' b x y); 
    set (fyz := f' b y z); 
    set (fxz := f' b x z); 
    destruct (f' b x y), (f' b y z);
        try (intro H; destruct H; discriminate);
        simpl.

(*
trans < Show.
1 subgoal

  b : bar
  x, y, z : t (convert b)
  e : x = y
  fxy := Eq e : dec_eq
  e0 : y = z
  fyz := Eq e0 : dec_eq
  fxz := f' b x z : dec_eq
  ============================
  true = true /\ true = true ->
  match fxz with
  | Eq _ => true
  | Neq _ => false
  end = true
*)

(* How can I use the equality e0 to show that (fxz = fxy)? *)
(*
21:42:28 < aweinstock> I've made a minimized example that gets a similar context to the full state that I'm trying: https://paste.rs/4zo
21:49:13 < aweinstock> in essence, I'm trying to prove a property about a function I'm universally quantifying over by extracting an equality witness from its output via (destruct (f x y)), and then trying to make use of that
                       equality witness to relate its other outputs
21:52:49 < aweinstock> the issue seems to be that the output I've added to the context with the `set` tactic and "evaluated" with the `destruct` tactic {loses, seems to lose} its provenance information
21:55:32 < aweinstock> concretely, in the linked paste, fxy and fyz have both been "evaluated", fxz hasn't been, (e0 : y=z) is in scope, and the unevaluated from of fxz is in the goal
21:55:39 < aweinstock> s/from of/form of/
21:58:40 < aweinstock> (I'm putting "evaluated" in quotes everywhere because I'm pretty sure that that's not quite the right word for case-analyzing the output of a function that's opaque due to quantification)
22:01:06 < aweinstock> my question is: is there some way, in that context, to make use of e0 to substitute fxy in place of fxz in that goal?
22:03:21 < dh`> I think you're framing it wrong
22:03:31 < aweinstock> (the unsimplified context is at https://paste.rs/ilg, in case it matters; cxy and cyz have different constructors in it)
22:03:34 < dh`> it goes through for me like this:
22:03:37 < dh`> (pasting in /msg)

22:03:46 <dh`>     intros x y z; simpl.
22:03:46 <dh`>     intro H. destruct H as [H1 H2].
22:03:46 <dh`>     destruct (f' b x y) eqn:Hfxy; try discriminate.
22:03:46 <dh`>     destruct (f' b y z) eqn:Hfyz; try discriminate.
22:03:46 <dh`>     subst. simpl.
22:03:46 <dh`>     rewrite Hfxy.
22:03:47 <dh`>     auto.
*)
    Restart. Set Ltac Debug.
    intros x y z; simpl.
    intro H. destruct H as [H1 H2].
    destruct (f' b x y) eqn:Hfxy; try discriminate.
    destruct (f' b y z) eqn:Hfyz; try discriminate.
    subst. simpl.
    rewrite Hfxy.
    auto.

(*
22:05:00 < dh`> does that not translate to the full context, or is the eqn:foo the critical part?
22:05:48 < aweinstock> I'm stepping through the proof you gave me to see if I can generalize it to the other case
22:05:55 < dh`> actually the "or" in that sentence is misleading
22:06:08 < dh`> probably what you want is specifically the eqn:foo part
22:08:19 < dh`> yes, it is.
22:10:59 < dh`> although the :='s produced with set are resistant to substitution and gunk it up
22:13:00 < dh`> yeah, besides that mine's only different from yours structurally
22:14:25 < aweinstock> it does seem to be a step in the right direction (on the non-simplified proof), though rewrites on the generated equations are failing (probably due to the different constructors)
22:14:56 < aweinstock> may I pm you the context/error message I'm getting now?
22:21:14 < aweinstock> the new context is at https://paste.rs/pt7
22:29:58 < dh`> that does not look promising
22:32:18 < dh`> first, check if 'subst' manages to do all the rewrites at once and avoid the problem (unlikely, but...)
22:33:26 < dh`> second, see if you can make an n': x <> z and then pcomp p x z = Less n'
22:33:48 < dh`> by explicitly asserting and proving them
22:33:51 < dh`> the second may be problematic
22:39:35 < aweinstock> 'subst' does the wrong direction (it makes Hyz refer to 'pcomp p z z'), but I'll try context management to flip it (with set/clear) and try again
22:41:35 < aweinstock> nope, clear can't get rid of the e' generated from (set (e' := eq_sym e)) due to the dependency on e
22:43:50 < aweinstock> (set (e' := eq_sym e); subst) did handle it though :)
22:46:22 < dh`> "symmetry in e" (or wherever) should fix the direction that subst causes
22:46:51 < dh`> that is, subst favors the left-hand side
22:47:18 < dh`> anyway if you can't get it to go, some of the techniques in here maybe useful: http://adam.chlipala.net/cpdt/html/Equality.html
22:47:36 < dh`> s/maybe/may be/
22:47:45 < aweinstock> subst isn't handling the next case (which is the last) with the set trick, and the 'symmetry in e' fails because other things reference e
22:48:09 < dh`> meh :(
22:49:25 < aweinstock> I have a copy of CPDT as a pdf, it looks like what you linked corresponds to chapter 10, I'll read that and keep fiddling with it
22:52:32 < aweinstock> another glance at the coq manual gave the 'subst ident' form, and I was able to finish the proof with it :)
*)
