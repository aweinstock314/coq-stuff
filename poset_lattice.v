Module Type POSET.
    Parameter t : Type.
    Parameter leq : t -> t -> bool.
    Axiom refl : forall x, leq x x = true.
    Axiom antisym : forall x y, leq x y = true /\ leq y x = true -> x = y.
    Axiom trans : forall x y z, leq x y = true /\ leq y z = true -> leq x z = true.
End POSET.

Module Type LATTICE.
    Declare Module L : POSET.
    Definition t : Type := L.t.
    Definition leq : t -> t -> bool := L.leq.

    Parameter glb lub : t -> t -> t.
    Parameter top bot : t.

    Axiom top_prop : forall x, leq x top = true.
    Axiom bot_prop : forall x, leq bot x = true.

    Axiom glb_prop1 : forall l1 l2, leq (glb l1 l2) l1 = true /\ leq (glb l1 l2) l2 = true.
    Axiom glb_prop2 : forall l1 l2 x, leq x l1 = true /\ leq x l2 = true -> leq x (glb l1 l2) = true.

    Axiom lub_prop1 : forall l1 l2, leq l1 (lub l1 l2) = true /\ leq l2 (lub l1 l2) = true.
    Axiom lub_prop2 : forall l1 l2 x, leq l1 x = true /\ leq l2 x = true -> leq (lub l1 l2) x = true.
End LATTICE.

Module PRODUCT_POSET (P1 P2 : POSET) : POSET.
    Definition t : Type := (P1.t * P2.t).
    Definition leq x y := andb (P1.leq (fst x) (fst y)) (P2.leq (snd x) (snd y)).

    Lemma lift_bool : forall b c : bool, andb b c = true -> b = true /\ c = true. (intros **; destruct b, c; inversion H; split; reflexivity). Qed.
    Lemma lift_leq : forall x y, leq x y = true -> P1.leq (fst x) (fst y) = true /\ P2.leq (snd x) (snd y) = true.
        (intros **).  (destruct x, y).  (compute).
        (cut (andb (P1.leq t0 t2) (P2.leq t1 t3) = true)).
        - specialize (lift_bool (P1.leq t0 t2) (P2.leq t1 t3)).  (intros **).  tauto.
        - (compute).  (apply H).
    Qed.

    Theorem refl : forall x, leq x x = true.
        (intros **).  (destruct x).  (compute).  (rewrite P1.refl).  (rewrite P2.refl).  reflexivity.
    Qed.
    Theorem antisym : forall x y, leq x y = true /\ leq y x = true -> x = y.
        intros; destruct x,y.
        cut (t0=t2 /\ t1=t3). intro H0; destruct H0; rewrite H0; rewrite H1; reflexivity.
        specialize (P1.antisym t0 t2). specialize (P2.antisym t1 t3). intros.
        (destruct H). (apply lift_leq in H; simpl in H). (apply lift_leq in H2; simpl in H2).
        tauto.
    Qed.
    Theorem trans : forall x y z, leq x y = true /\ leq y z = true -> leq x z = true.
        (intros **). (destruct x, y, z).
        specialize (P1.trans t0 t2 t4). specialize (P2.trans t1 t3 t5). (intros **).
        (destruct H).
        unfold leq; simpl.
        (apply lift_leq in H). (apply lift_leq in H2).
        (simpl in H, H2). (destruct H, H2).
        (rewrite H, H2 in H1). (rewrite H3, H4 in H0).
        (destruct H0). tauto. (destruct H1). tauto.
        (destruct (P1.leq t0 t4); tauto).
    Qed.
End PRODUCT_POSET.

(*
Module PRODUCT_LATTICE (L1 L2 : LATTICE) : LATTICE.
    
End PRODUCT_LATTICE.
*)
