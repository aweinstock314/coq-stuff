(*
Logic puzzle from "Fundamental Proof Methods in Computer Science (Arkoudas and Musser)":
    Jack is looking at Anne, and Anne is looking at George.
    Jack is married, George is not. Is some married person
    looking at an unmarried person?
 *)
Module Chap1LogicPuzzle.

Axiom LEM : forall p, p \/ ~p.

Axiom Person : Set.
Axiom Anne George Jack : Person.

Axiom Married : Person -> Prop.
Axiom LookingAt : Person -> Person -> Prop.

Theorem puzzle : (LookingAt Jack Anne /\ LookingAt Anne George /\ Married Jack /\ ~Married George) -> exists p q, Married p /\ ~Married q /\ LookingAt p q.
    intro Hyp1; decompose [and] Hyp1; (* unpackage all the LookingAt's and Married's from /\'s into the environment *)
    specialize (LEM (Married Anne)) as Hyp2; destruct Hyp2; (* set up the case split on (Married Anne \/ ~Married Anne), and create the 2 subgoals from it *)
    [exists Anne, George (* Solve the (Married Anne) case with p=Anne, q=George *)
    | exists Jack, Anne]; (* Solve the (~Married Anne) case with p=Jack, q=Anne *)
    tauto.  (* repackage the components in the environment into /\'s *)
    Qed.

End Chap1LogicPuzzle.
Import Chap1LogicPuzzle.

(*
The following commands can be run after invoking `rlwrap coqtop -l chap1_logicpuzzle.v`:
Print Module Chap1LogicPuzzle.
Print puzzle.
*)
