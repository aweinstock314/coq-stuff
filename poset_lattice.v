Record POSET : Type := mkPoset {
    t : Type;
    leq : t -> t -> bool;
    refl : forall x, leq x x = true;
    antisym : forall x y, leq x y = true /\ leq y x = true -> x = y;
    trans : forall x y z, leq x y = true /\ leq y z = true -> leq x z = true;
    }.

Record LATTICE : Type := mkLattice {
    L : POSET;
    top : t L;
    bot : t L;

    glb : t L -> t L -> t L;
    lub : t L -> t L -> t L;

    top_prop : forall x, leq L x top = true;
    bot_prop : forall x, leq L bot x = true;

    glb_prop1 : forall l1 l2, leq L (glb l1 l2) l1 = true /\ leq L (glb l1 l2) l2 = true;
    glb_prop2 : forall l1 l2 x, leq L x l1 = true /\ leq L x l2 = true -> leq L x (glb l1 l2) = true;

    lub_prop1 : forall l1 l2, leq L l1 (lub l1 l2) = true /\ leq L l2 (lub l1 l2) = true;
    lub_prop2 : forall l1 l2 x, leq L l1 x = true /\ leq L l2 x = true -> leq L (lub l1 l2) x = true;
    }.

Module PRODUCT_POSET_THEOREMS.
    Definition product_leq P1 P2 x y := andb (leq P1 (fst x) (fst y)) (leq P2 (snd x) (snd y)).

    Lemma lift_bool : forall b c : bool, andb b c = true -> b = true /\ c = true. (intros **; destruct b, c; inversion H; split; reflexivity). Qed.
    Lemma lift_leq (P1 P2 : POSET) : forall x y, product_leq P1 P2 x y = true -> leq P1 (fst x) (fst y) = true /\ leq P2 (snd x) (snd y) = true.
        intros **.  (destruct x, y).  (compute).
        (cut (andb (leq P1 t0 t2) (leq P2 t1 t3) = true)).
        - specialize (lift_bool (leq P1 t0 t2) (leq P2 t1 t3)).  intros **.  tauto.
        - (compute).  (apply H).
    Qed.

    Theorem refl (P1 P2 : POSET) : forall x, product_leq P1 P2 x x = true.
        intros **.  (destruct x).  (compute).  (rewrite (refl P1)).  (rewrite (refl P2)).  reflexivity.
    Qed.
    Theorem antisym (P1 P2 : POSET) : forall x y, product_leq P1 P2 x y = true /\ product_leq P1 P2 y x = true -> x = y.
        intros; destruct x,y.
        cut (t0=t2 /\ t1=t3). intro H0; destruct H0; rewrite H0; rewrite H1; reflexivity.
        specialize (antisym P1 t0 t2). specialize (antisym P2 t1 t3). intros.
        (destruct H). (apply (lift_leq P1 P2) in H; simpl in H). (apply (lift_leq P1 P2) in H2; simpl in H2).
        tauto.
    Qed.

    Theorem trans (P1 P2 : POSET) : forall x y z, product_leq P1 P2 x y = true /\ product_leq P1 P2 y z = true -> product_leq P1 P2 x z = true.
        intros **. (destruct x, y, z).
        specialize (trans P1 t0 t2 t4). specialize (trans P2 t1 t3 t5). intros **.
        destruct H.
        unfold product_leq; simpl.
        (apply lift_leq in H). (apply lift_leq in H2).
        (simpl in H, H2). (destruct H, H2).
        (rewrite H, H2 in H1). (rewrite H3, H4 in H0).
        (destruct H0). tauto. (destruct H1). tauto.
        (destruct (leq P1 t0 t4); tauto).
    Qed.
End PRODUCT_POSET_THEOREMS.

Definition PRODUCT_POSET (P1 P2 : POSET) : POSET := mkPoset (t P1 * t P2) (PRODUCT_POSET_THEOREMS.product_leq P1 P2)
    (PRODUCT_POSET_THEOREMS.refl P1 P2) (PRODUCT_POSET_THEOREMS.antisym P1 P2) (PRODUCT_POSET_THEOREMS.trans P1 P2).

Module PRODUCT_LATTICE_THEOREMS.
    Definition top L1 L2 := (top L1, top L2).
    Definition bot L1 L2:= (bot L1, bot L2).

    Definition glb L1 L2 x y := (glb L1 (fst x) (fst y), glb L2 (snd x) (snd y)).
    Definition lub L1 L2 x y := (lub L1 (fst x) (fst y), lub L2 (snd x) (snd y)).
End PRODUCT_LATTICE_THEOREMS.

(*
Definition PRODUCT_LATTICE (L1 L2 : LATTICE) : LATTICE := mkLattice (PRODUCT_POSET (L L1) (L L2))
    (PRODUCT_LATTICE_THEOREMS.top L1 L2) (PRODUCT_LATTICE_THEOREMS.bot L1 L2)
    (PRODUCT_LATTICE_THEOREMS.glb L1 L2) (PRODUCT_LATTICE_THEOREMS.lub L1 L2)
    _ _ _ _ _ _.
*)
