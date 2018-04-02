(*
08:45:57 < Gurkenglas> Can Coq talk about provability in Coq?
09:48:06 < aweinstock> Gurkenglas: I'd assume you can encode CIC derivation trees as an Inductive, and I'd also assume (via Godel's theorems) that there's a limit to what can be proved using that approach, but I don't know a 
                       concrete example
09:54:23 < Gurkenglas> Hmm, there'd be forall a, Provable a -> a which evals the proof, for each a there'd be Provable a, there'd be Provable a -> Provable (Provable a) and (a -> b) -> Provable a -> Provable b
09:54:35 < Gurkenglas> Did I miss anything that can't be derived from these?
09:55:01 < Gurkenglas> forall a and forall a b respectively on the last two
09:58:52 < aweinstock> which modal logic do those 4 correspond to?
09:59:24 < aweinstock> (m a -> a, a -> m a, m a -> m (m a), (a -> b) -> (m a -> m b))
09:59:38 < Gurkenglas> I don't know, I pulled these out of my hat, using Haskell's Functor-Monad hierarchy for inspiration
09:59:59 < Gurkenglas> And I don't think there'd be forall a, a -> m a, just for each a there'd be m a
10:00:04 < aweinstock> isn't (Provable a -> Provable (Provable a)) redundant given (a -> Provable a)?
10:00:05 < aweinstock> ah
10:04:13 < aweinstock> Gurkenglas: if you can find a copy of "The logic of provability" by George Boolos, it's a decent read on a modal logic treatment of provability
10:07:39 < aweinstock> just found a relevant passage: "either GL is inconsistent or some sentence (m a -> a) is not a theorem of GL or some sentence (m (m a -> a)) is not a theorem of GL" (I'm transcribing the box symbols as 
                       m)
10:11:35 < Gurkenglas> That seems surprising. Is this constructive? What would it construct for the obvious implementation for Coq?
10:14:06 < aweinstock> I'm not entirely sure, I read the first few chapters months ago, and just got it out now to try to use it as a reference; I'd like to do the exercises from it in Coq at some point, but haven't yet found 
                       the time
10:14:22 < benzrf> Provable a -> a implies that we know that our ambient logic is a model of CIC, but im not convinced that we do know that
10:15:43 < Gurkenglas> I'm not sure about the things you said after Provable a -> a, but why couldn't you just translate each constructor of Provable a into the corresponding tactic?
10:15:45 < aweinstock> yeah, that one seemed the sketchiest of the four to me (on more heuristic grounds, e.g. looking like the type of unsafePerformIO)
10:16:20 < benzrf> Gurkenglas: that only makes sense from an external standpoint
10:17:29 < benzrf> if you try to write a function that recurses over the tree and implements it, i wouldn't be surprised if that's impossible within the type system
10:17:48 < benzrf> eval in general tends to be unsound
10:17:55 < Gurkenglas> I mean... if you ignore any standpoints but the external, whatever that means, and just implement Provable a -> a that way, and apply that "either GL is inconsistent or...", what pathological 
                       construction do you get?
10:18:07 < benzrf> you might get infinite looping
10:18:27 < benzrf> actually now i'm not sure
10:18:40 < benzrf> but i wouldn't be surprised if some sort of universe-related nonsense crops up
10:20:02 < Gurkenglas> Is infinite looping possible within Coq? Is the Universe checking just a safeguard or does something rely on it? What pathology would pop up if you override the safeguard?
10:20:25 < modulus> iirc isn't infinite looping equiva to proof of alse?
10:20:32 < benzrf> https://en.wikipedia.org/wiki/System_U#Girard's_paradox
10:21:04 < benzrf> modulus: i dunno, i can imagine some sort of thing where you can get an infinite loop but not one whose type is False
10:22:04 < benzrf> Gurkenglas: sorry that link might be unhelpful, i've never actually read the proof myself
10:22:20 < aweinstock> Gurkenglas: the statement I quoted has a proof sketch right afterwards, I'll try to photograph the page
10:22:22 < benzrf> but a simple type theory where Type : Type is known to be inconsistent
10:22:53 < benzrf> that's why you need a cumulative hierarchy, or alternatively some sort of restriction on quantification i guess
10:23:38 < benzrf> it's analogous to russell's paradox apparently
10:23:54 < Gurkenglas> aweinstock, just found one, which page?
10:25:25 < aweinstock> Gurkenglas: page 1 (the intro page right before it is xxxvi)
10:55:55 < Gurkenglas> "either GL is inconsistent or some sentence (m a -> a) is not a theorem of GL or some sentence (m (m a -> a)) is not a theorem of GL" requires m (m a -> a) -> m a, how does this apply to Coq?
10:56:55 < Gurkenglas> -requires+assumes in that book
10:57:12 < Gurkenglas> Better question: What system of propositional modal logic, if any, corresponds to Coq?
*)
Goal ~(forall (m : Prop -> Prop) (a : Prop), (m a -> a) /\ m (m a -> a)).
    intro H.
    Check H (fun x => x).
    Check H (fun _ => False).
    exact (proj2 (H (fun _ => False) True)).
    Qed.

Definition foo : ~(forall (m : Prop -> Prop) (a : Prop), (m a -> a) /\ m (m a -> a)) := fun H => proj2 (H (fun _ => False) True).

(*Goal forall (m : Type -> Type), (forall (a : Type), prod (m a -> a) (m (m a -> a))) -> False.*)
(*
11:05:46 < aweinstock> Gurkenglas: "~(forall (m : Prop -> Prop) (a : Prop), (m a -> a) /\ m (m a -> a))" is inhabited by "fun H => proj2 (H (fun _ => False) True)", but that might be too weak a placement of the quantifiers
11:16:39 < aweinstock> Gurkenglas: I'm trying to work with the stronger `Goal forall (m : Prop -> Prop), ~(forall (a : Prop), (m a -> a) /\ m (m a -> a)).` now, not sure whether or not to expect it to be provable yet
11:24:10 < aweinstock> Gurkenglas: page xvii asserts that "The sentence (m p -> p) is not a theorem of GL" (with the same transcription thing about m representing box)
*)

Axiom GL_distribution : forall (m : Prop -> Prop) (a b : Prop), m (a -> b) -> (m a -> m b). (* corresponds to Applicative's <*> *)

Definition tmp := forall (m : Prop -> Prop), ~(forall (a : Prop), (m a -> a) /\ m (m a -> a)).
Goal tmp.
    intros m H.
    (*Check H False.  Check H (m False). *)
    set (H' := fun a => H (m a)).
    set (join := fun a => GL_distribution _ _ _ (proj2 (H a))).
    set (runM := fun a => proj1 (H a)).
    (destruct (H False) as [f g]).
    (destruct (H (m False)) as [x y]).
    Abort.
(*
11:41:48 < Gurkenglas> aweinstock, Goal ~(forall (m : Prop -> Prop), ~(forall (a : Prop), (m a -> a) /\ m (m a -> a))). intuition. refine (H _ _). intuition. exact H0. simpl. intuition. Qed.
*)

Goal ~tmp.
    intuition. refine (H _ _). intuition. exact H0. simpl. intuition.
    Qed.
(*
11:46:18 < Gurkenglas> But obviously you're not going to get something useful out of this without assuming more about m. What's Coqs propositional modal logic?
11:48:31 < Gurkenglas> Though the absence of a -> Provable a does not feel necessary for Coq, it just happens to be true right now
11:48:53 < Gurkenglas> We could carry a proof around with each value and make it accessible to the user
11:51:53 < aweinstock> I'm not sure that GL's metatheory is applicable to CIC, but if it is, then we have additional evidence that (Provable a -> a) isn't Coq-provable
11:55:45 < Gurkenglas> Which means that I have evidence that GL's metatheory is not applicable to CIC :D
11:58:04 < aweinstock> so, you're going to try inhabiting (Provable a -> a), where Provable is some datatype that encodes CIC-derivation-trees?
12:00:12 < Gurkenglas> I don't think I'm qualified for that, as I don't even know exactly what CIC-derivation-trees are - but how could it possibly be hard to - oh, actually I guess some of the typechecking might be hard.
12:01:31 < Gurkenglas> I missed that the inductive Provable datatype I had in mind wouldn't just contain well-formed proofs, just Coq files.
12:04:34 < aweinstock> page 115 of https://web.archive.org/web/20151210043636/https://coq.inria.fr/distrib/current/files/Reference-Manual.pdf
12:05:16 < aweinstock> (the thing in my local copy is page 124, so grab an updated copy once the inria site comes back up)
12:05:47 < aweinstock> it's the typing rules for CIC, presented in a logical deduction style
12:05:56 < aweinstock> s/logical/natural/
*)
