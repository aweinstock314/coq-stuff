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

    glb_prop1 : forall x y, leq L (glb x y) x = true /\ leq L (glb x y) y = true;
    glb_prop2 : forall x y a, leq L a x = true /\ leq L a y = true -> leq L a (glb x y) = true;

    lub_prop1 : forall x y, leq L x (lub x y) = true /\ leq L y (lub x y) = true;
    lub_prop2 : forall x y a, leq L x a = true /\ leq L y a = true -> leq L (lub x y) a = true;
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
    Definition L' L1 L2 := PRODUCT_POSET (L L1) (L L2).
    Definition top L1 L2 := (top L1, top L2).
    Definition bot L1 L2 := (bot L1, bot L2).

    Definition glb L1 L2 x y := (glb L1 (fst x) (fst y), glb L2 (snd x) (snd y)).
    Definition lub L1 L2 x y := (lub L1 (fst x) (fst y), lub L2 (snd x) (snd y)).

    Ltac topbot L1 L2 which_prop which := 
        simpl; specialize (which_prop L1); specialize (which_prop L2); intros H H0 x;
        unfold which; unfold PRODUCT_POSET_THEOREMS.product_leq;
        destruct x as [t0 t1]; simpl;
        specialize (H0 t0); specialize (H t1);
        rewrite H0; rewrite H;
        reflexivity.

    Theorem top_prop L1 L2 : forall x, leq (L' L1 L2) x (top L1 L2) = true. topbot L1 L2 top_prop top. Qed.
    Theorem bot_prop L1 L2 : forall x, leq (L' L1 L2) (bot L1 L2) x = true. topbot L1 L2 bot_prop bot. Qed.

    Ltac prop1 L1 L2 which_prop1 := 
        intros x y; destruct x as [x1 x2], y as [y1 y2];

        (* surprisingly, it doesn't work with either of these (even though they worked interactively) *)
        (*specialize (which_prop1 L1) as H1; specialize (which_prop1 L2) as H2; *)
        (*specialize (which_prop1 L1); intro H1; specialize (which_prop1 L2); intro H2;*)
        (* it works with the following though *)
        specialize (which_prop1 L1); specialize (which_prop1 L2); intros H2 H1;

        specialize (H1 x1 y1); specialize (H2 x2 y2);
        simpl; unfold PRODUCT_POSET_THEOREMS.product_leq; simpl;
        destruct H1 as [Ha Hb]; destruct H2 as [Hc Hd]; rewrite Ha, Hb, Hc, Hd;
        tauto.


    Theorem glb_prop1 L1 L2 : forall x y, leq (L' L1 L2) (glb L1 L2 x y) x = true /\ leq (L' L1 L2) (glb L1 L2 x y) y = true.  prop1 L1 L2 glb_prop1.  Qed.
    Theorem lub_prop1 L1 L2 : forall x y, leq (L' L1 L2) x (lub L1 L2 x y) = true /\ leq (L' L1 L2) y (lub L1 L2 x y) = true.  prop1 L1 L2 lub_prop1.  Qed.

(*
End PRODUCT_LATTICE_THEOREMS.

*)
(*
Definition PRODUCT_LATTICE (L1 L2 : LATTICE) : LATTICE := mkLattice (PRODUCT_POSET (L L1) (L L2))
    (PRODUCT_LATTICE_THEOREMS.top L1 L2) (PRODUCT_LATTICE_THEOREMS.bot L1 L2)
    (PRODUCT_LATTICE_THEOREMS.glb L1 L2) (PRODUCT_LATTICE_THEOREMS.lub L1 L2)
    (PRODUCT_LATTICE_THEOREMS.top_prop L1 L2) (PRODUCT_LATTICE_THEOREMS.bot_prop L1 L2)
    (PRODUCT_LATTICE_THEOREMS.glb_prop1 L1 L2) _ 
    (PRODUCT_LATTICE_THEOREMS.lub_prop1 L1 L2) _.
*)
