Require Import Coq.Program.Tactics.

Record POSET : Type := mkPoset {
    t : Type;
    leq : t -> t -> bool;
    }.
Record POSET_PROOFS : Type := mkPosetProofs {
    P : POSET;
    refl : forall x, leq P x x = true;
    antisym : forall x y, leq P x y = true -> leq P y x = true -> x = y;
    trans : forall x y z, leq P x y = true -> leq P y z = true -> leq P x z = true;
    }.

Inductive Pord {A : Type} {x y : A} :=
      Less : (x <> y) -> Pord
    | Equal : (x = y) -> Pord
    | Greater : (x <> y) -> Pord
    | Uncomparable : (x <> y) -> Pord.

Record POSET' : Type := mkPoset' {
    t' : Type;
    pcomp : forall (x y : t'), @ Pord t' x y;
    trans_l : forall x y z, { nxy | pcomp x y = Less nxy } -> { nyz | pcomp y z = Less nyz } -> { nxz | pcomp x z = Less nxz };
    }.

Module POSET_ISOMORPHISMS.
    Definition to_leq (p : POSET') := fun x y => match pcomp p x y with Less _ => true | Equal _ => true | _ => false end.
    Definition to' (p : POSET') : POSET := {| t := t' p; leq := to_leq p |}.

    Theorem orig_refl (p : POSET') : forall x, {e : x = x | pcomp p x x = Equal e}.
        intro x. destruct (pcomp p x x); try contradiction. exists e. reflexivity. Qed.
    Theorem to_refl (p : POSET') : forall x, leq (to' p) x x = true.
        intro x; simpl; unfold to_leq; destruct (pcomp p x x); try contradiction; reflexivity. Qed.
    Theorem to_antisym (p : POSET') : forall x y, leq (to' p) x y = true -> leq (to' p) y x = true -> x = y.
        intros x y; simpl; unfold to_leq.
        specialize (trans_l p x y x) as trans_l_instance.
        destruct (pcomp p x y), (pcomp p y x); (* 4*4 = 16 cases to handle *)
            try [> intros H H'; discriminate]; (* all 12 cases involving Greater/Uncomparable follow vacuously *)
            try [> intros; try exact e; exact (eq_sym e)]. (* all 3 remaining cases involving an equality are resolved from the witness *)
        (* in the Less/Less case, x < y & y < x, leading (by trans_l) x < x, which violates reflexivity *)
        destruct (trans_l_instance (exist _ n eq_refl) (exist _ n0 eq_refl)); contradiction.
        Qed.
    Theorem to_trans (p : POSET') : forall x y z, leq (to' p) x y = true -> leq (to' p) y z = true -> leq (to' p) x z = true.
        intros x y z; simpl; unfold to_leq.
        specialize (trans_l p x y z) as trans_l_instance.
        destruct (pcomp p x y) eqn:Hxy, (pcomp p y z)eqn:Hyz;
            try [> intros; discriminate]; (* handle the trivially vacuous cases *)
            try [> intros; reflexivity]; (* handle the remaining equality cases *)
            match goal with
            | _:pcomp p x y = Less _, _:pcomp p y z = Less _ |- _ => destruct (trans_l_instance (exist _ n eq_refl) (exist _ n0 eq_refl)); try discriminate; (rewrite e; reflexivity)
            | exy:x=y, eyz:y=z, nxz:x<>z |- _  => destruct (nxz (eq_trans exy eyz))
            | e:_=_, H:pcomp _ _ _ = Less _ |- _ => subst; rewrite H; reflexivity
            | exy:x=y, eyz:y=z |- _ => rewrite (eq_trans exy eyz); destruct (orig_refl p z) as [x' e']; rewrite e'; reflexivity
        end. Qed.
    Definition to (p : POSET') : POSET_PROOFS := {| P := to' p; refl := to_refl p; antisym := to_antisym p; trans := to_trans p |}.

    Theorem leq_false_neq (p : POSET_PROOFS) : forall x y, leq (P p) x y = false -> x <> y.
        intros x y Hleq exy; rewrite exy, (refl p y) in Hleq; discriminate. Qed.
    Definition neq_sym {A : Type} {x y : A} (n : x <> y) : (y <> x) := fun e => n (eq_sym e).

    Definition or_intro1 {P Q R S : Prop} (x : P) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition or_intro2 {P Q R S : Prop} (x : Q) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition or_intro3 {P Q R S : Prop} (x : R) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition or_intro4 {P Q R S : Prop} (x : S) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition from_leq' (p : POSET_PROOFS) : forall x y, { r : @Pord (t (P p)) x y |
        (exists e : x = y, r = Equal e /\ (leq (P p) x y, leq (P p) y x) = (true, true)) \/
        (exists n : x <> y, r = Less n /\ (leq (P p) x y, leq (P p) y x) = (true, false)) \/
        (exists n : x <> y, r = Greater n /\ (leq (P p) x y, leq (P p) y x) = (false, true)) \/
        (exists n : x <> y,  r = Uncomparable n /\ (leq (P p) x y, leq (P p) y x) = (false, false))} :=
        fun x y => let leqs := (leq (P p) x y, leq (P p) y x) in
        match leqs as bools return (leqs = bools) -> _ with
            | (true, true) => fun e => let e' := (antisym p x y (f_equal fst e) (f_equal snd e)) in
                exist _ (Equal e') (or_intro1 (ex_intro _ e' (conj eq_refl e)))
            | (true, false) => fun e => let n := (neq_sym (leq_false_neq p y x (f_equal snd e))) in
                exist _ (Less n) (or_intro2 (ex_intro _ n (conj eq_refl e)))
            | (false, true) => fun e => let n := (leq_false_neq p x y (f_equal fst e)) in
                exist _ (Greater n) (or_intro3 (ex_intro _ n (conj eq_refl e)))
            | (false, false) => fun e => let n := (leq_false_neq p x y (f_equal fst e)) in
                exist _ (Uncomparable n) (or_intro4 (ex_intro _ n (conj eq_refl e)))
        end eq_refl.
    Definition from_leq (p : POSET_PROOFS) : forall x y, @Pord (t (P p)) x y := fun x y => match from_leq' p x y with exist _ ord _ => ord end.
    Theorem leq_implies_from_leq (p : POSET_PROOFS) : forall x y, leq (P p) x y = true -> { n | from_leq p x y = Less n } \/ { e | from_leq p x y = Equal e }.
        intros x y Hleq. remember (from_leq p x y) as result eqn:foo1.
        unfold from_leq in foo1.
        destruct (from_leq' p x y) eqn:foo2; decompose [or] o.
        - destruct H as [x1 a]. right. exists x1. rewrite <- foo1 in a. exact (proj1 a).
        - destruct H0 as [x1 a]. left. exists x1. rewrite <- foo1 in a. exact (proj1 a).
        - destruct H as [x1 a]. destruct a. remember (f_equal fst H0). simpl in e. rewrite e in Hleq. discriminate Hleq.
        - destruct H as [x1 a]. destruct a. remember (f_equal fst H0). simpl in e. rewrite e in Hleq. discriminate Hleq.
        Qed.
    Theorem from_trans (p : POSET_PROOFS) : forall x y z, { nxy | from_leq p x y = Less nxy } -> { nyz | from_leq p y z = Less nyz } -> { nxz | from_leq p x z = Less nxz }.
        intros x y z Hxy Hyz. destruct Hxy as [nxy lxy], Hyz as [nyz lyz].
        remember (from_leq p x y) as rxy eqn:eqxy; remember (from_leq p y z) as ryz eqn:eqyz; remember (from_leq p x z) as rxz eqn:eqxz.
        unfold from_leq in eqxy, eqyz, eqxz.
        destruct (from_leq' p x y), (from_leq' p y z), (from_leq' p x z).
        decompose [and or] (conj o (conj o0 o1)); match goal with
        | n:(?x <> ?y), H:(exists _ : ?x = ?y, _) |- _ => destruct H as [e _]; destruct (n e)
        | l:(?r = Less _), e:(?r = ?x), H:(exists _, ?x = (* Equal/Greater/Uncomparable *) _ /\ _) |- _ =>
            destruct H as [a b]; rewrite e in l; rewrite (proj1 b) in l; discriminate l
        | Hxy:(exists _,_ /\ (leq (P p) x y, _) = (true, _)), Hyz:(exists _,_ /\ (leq (P p) y z, _) = (true, _)), Hxz:(exists _,_ /\ (leq (P p) x z, _) = (false, _)) |- _ =>
            destruct Hxy as [axy bxy]; destruct Hyz as [ayz byz]; destruct Hxz as [axz bxz];
            discriminate (eq_stepl (trans p x y z (f_equal fst (proj2 bxy)) (f_equal fst (proj2 byz))) (f_equal fst (proj2 bxz)))
        | Hxy:(exists _,_ /\ (leq (P p) x y, _) = (true, _)), Hyz:(exists _,_ /\ (leq (P p) y z, _) = (true, _)), Hxz:(exists _,_ /\ (_, leq (P p) z x) = (_, true)), nxy:(x <> y) |- _ =>
            destruct Hxy as [axy bxy]; destruct Hyz as [ayz byz]; destruct Hxz as [axz bxz];
            set (leqyx := trans p y z x (f_equal fst (proj2 byz)) (f_equal snd (proj2 bxz)));
            set (exy := antisym p x y (f_equal fst (proj2 bxy)) leqyx);
            destruct (nxy (exy))
        | H:(exists _,?x = Less _ /\ _), e:(?r = ?x) |- {_|?r = Less _} => destruct H as [a b]; exists a; rewrite e, (proj1 b); reflexivity
        end.
        Qed.
    Definition from (p : POSET_PROOFS) : POSET' := {| t' := t (P p); pcomp := from_leq p; trans_l := from_trans p |}.
End POSET_ISOMORPHISMS.

Definition GaloisConnection (C A : POSET_PROOFS) (abs : t (P C) -> t (P A)) (conc : t (P A) -> t (P C)) : Prop :=
    forall (a : t (P A)) (c : t (P C)), leq _ c (conc a) = true <-> leq _ (abs c) a = true.

Theorem galois_composition : forall A B C a1 c1 a2 c2, GaloisConnection A B a1 c1 -> GaloisConnection B C a2 c2 -> GaloisConnection A C (fun a => a2 (a1 a)) (fun c => c1 (c2 c)).
    intros A B C a1 c1 a2 c2 gcab gcbc c a.
    exact (iff_trans (gcab (c2 c) a) (gcbc c (a1 a))).
    Qed.

Definition Monotone {p q : POSET_PROOFS} (f : t (P p) -> t (P q)) : Prop := forall x y, leq _ x y = true -> leq _ (f x) (f y) = true.

Theorem galois_contractive {A C : POSET_PROOFS} abs conc (gc : GaloisConnection C A abs conc) a : leq _ (abs (conc a)) a = true.
    exact (proj1 (gc _ _) (refl C (conc a))). Qed.
Theorem galois_expansive {A C : POSET_PROOFS} abs conc (gc : GaloisConnection C A abs conc) c : leq _ c (conc (abs c)) = true.
    exact (proj2 (gc _ _) (refl A (abs c))). Qed.

Theorem galois_monotone : forall A C abs conc, GaloisConnection C A conc abs -> Monotone abs /\ Monotone conc.
    split; intros x y Hleq.
    - exact (proj2 (H y (abs x)) (trans _ _ _ _ (galois_contractive _ _ H x) Hleq)).
    - exact (proj1 (H (conc y) x) (trans _ _ _ _ Hleq (galois_expansive conc abs H y))).
    Qed.

Record LATTICE : Type := mkLattice {
    L : POSET;
    top : t L;
    bot : t L;
    glb : t L -> t L -> t L;
    lub : t L -> t L -> t L;
    }.
Record LATTICE_PROOFS : Type := mkLatticeProofs {
    lat : LATTICE;
    pos : { p : POSET_PROOFS | L lat = P p };
    top_prop : forall x, leq (L lat) x (top lat) = true;
    bot_prop : forall x, leq (L lat) (bot lat) x = true;

    glb_prop1 : forall x y, leq (L lat) ((glb lat) x y) x = true /\ leq (L lat) ((glb lat) x y) y = true;
    glb_prop2 : forall x y a, leq (L lat) a x = true /\ leq (L lat) a y = true -> leq (L lat) a ((glb lat) x y) = true;

    lub_prop1 : forall x y, leq (L lat) x ((lub lat) x y) = true /\ leq (L lat) y ((lub lat) x y) = true;
    lub_prop2 : forall x y a, leq (L lat) x a = true /\ leq (L lat) y a = true -> leq (L lat) ((lub lat) x y) a = true;
    }.

Module LATTICE_M.
    (*Definition wit {T : Type} {P : T -> Prop} {y : T} (x : { y : T | P y }) : T := match x with exist _ t _ => t end.*)
    Ltac both_idempotent which prop1 prop2 :=
        intros LP x; destruct (pos LP) as [PP e];
        specialize (prop1 LP x x); specialize (prop2 LP x x x);
        specialize (refl PP); intros Hr; rewrite <- e in Hr; specialize (Hr x);
        specialize (antisym PP); intros Has; rewrite <- e in Has; specialize (Has x (which (lat LP) x x));
        tauto.
    Theorem glb_idempotent : forall (LP : LATTICE_PROOFS) x, x = glb (lat LP) x x. both_idempotent glb glb_prop1 glb_prop2. Qed.
    Theorem lub_idempotent : forall (LP : LATTICE_PROOFS) x, x = lub (lat LP) x x. both_idempotent lub lub_prop1 lub_prop2. Qed.

    Ltac leq_both_eq which prop :=
        intros LP x H; destruct (pos LP) as [PP e];
        specialize (prop LP x); intro;
        specialize (antisym PP); intros Has; rewrite <- e in Has; specialize (Has x (which (lat LP)));
        tauto.
    Theorem leq_top_eq : forall (LP : LATTICE_PROOFS) x, leq (L (lat LP)) (top (lat LP)) x = true -> x = (top (lat LP)). leq_both_eq top top_prop. Qed.
    Theorem leq_bot_eq : forall (LP : LATTICE_PROOFS) x, leq (L (lat LP)) x (bot (lat LP)) = true -> x = (bot (lat LP)). leq_both_eq bot bot_prop. Qed.
End LATTICE_M.

Module PRODUCT_POSET_M.
    Definition product_leq P1 P2 x y := andb (leq P1 (fst x) (fst y)) (leq P2 (snd x) (snd y)).

    Lemma lift_bool : forall b c : bool, andb b c = true -> b = true /\ c = true. (intros **; destruct b, c; inversion H; split; reflexivity). Qed.
    Lemma lift_leq (P1 P2 : POSET) : forall x y, product_leq P1 P2 x y = true -> leq P1 (fst x) (fst y) = true /\ leq P2 (snd x) (snd y) = true.
        intros **.  (destruct x, y).  (compute).
        (cut (andb (leq P1 t0 t2) (leq P2 t1 t3) = true)).
        - specialize (lift_bool (leq P1 t0 t2) (leq P2 t1 t3)).  intros **.  tauto.
        - (compute).  (apply H).
    Qed.
    Lemma lift_leq' (P1 P2 : POSET) : forall x y, leq P1 (fst x) (fst y) = true /\ leq P2 (snd x) (snd y) = true -> product_leq P1 P2 x y = true.
        intros x y H.  destruct x as [x1 x2], y as [y1 y2].
        simpl in H.  destruct H as [H1 H2].
        unfold product_leq. simpl. rewrite H1; rewrite H2.
        tauto.
    Qed.

    Theorem refl (P1 P2 : POSET_PROOFS) : forall x, product_leq (P P1) (P P2) x x = true.
        intros **.  (destruct x).  (compute).  (rewrite (refl P1)).  (rewrite (refl P2)).  reflexivity.
    Qed.
    Theorem antisym (P1 P2 : POSET_PROOFS) : forall x y, product_leq (P P1) (P P2) x y = true -> product_leq (P P1) (P P2) y x = true -> x = y.
        intros x y Hxy Hyx.
        destruct (lift_leq _ _ x y Hxy) as [Hxy1 Hxy2], (lift_leq _ _ y x Hyx) as [Hyx1 Hyx2].
        destruct x as [x1 x2], y as [y1 y2]. simpl in *.
        rewrite (antisym _ _ _ Hxy1 Hyx1), (antisym _ _ _ Hxy2 Hyx2).
        reflexivity.
    Qed.

    Theorem trans (P1 P2 : POSET_PROOFS) : forall x y z, product_leq (P P1) (P P2) x y = true -> product_leq (P P1) (P P2) y z = true -> product_leq (P P1) (P P2) x z = true.
        intros **. (destruct x, y, z).
        specialize (trans P1 t0 t2 t4). specialize (trans P2 t1 t3 t5). intros **.
        unfold product_leq; simpl.
        (apply lift_leq in H). (apply lift_leq in H0).
        (simpl in H, H0). (destruct H, H0).
        (rewrite H, H0 in H2). (rewrite H3, H4 in H1).
        (destruct H2, H1); try tauto.
        match goal with |- (?b && ?b)%bool = ?b => destruct b; tauto end.
    Qed.
End PRODUCT_POSET_M.

Definition PRODUCT_POSET (P1 P2 : POSET) : POSET := {|
    t := t P1 * t P2;
    leq := PRODUCT_POSET_M.product_leq P1 P2;
    |}.
Definition PRODUCT_POSET_PROOFS (P1 P2 : POSET_PROOFS) : POSET_PROOFS := {|
    P := PRODUCT_POSET (P P1) (P P2);
    refl := PRODUCT_POSET_M.refl P1 P2;
    antisym := PRODUCT_POSET_M.antisym P1 P2;
    trans := PRODUCT_POSET_M.trans P1 P2
    |}.

Module PRODUCT_LATTICE_M.
    Definition L' L1 L2 := PRODUCT_POSET (L L1) (L L2).
    Definition top L1 L2 := (top L1, top L2).
    Definition bot L1 L2 := (bot L1, bot L2).

    Definition glb L1 L2 x y := (glb L1 (fst x) (fst y), glb L2 (snd x) (snd y)).
    Definition lub L1 L2 x y := (lub L1 (fst x) (fst y), lub L2 (snd x) (snd y)).

    Ltac topbot L1 L2 which_prop which :=
        simpl; specialize (which_prop L1); specialize (which_prop L2); intros H H0 x;
        unfold which; unfold PRODUCT_POSET_M.product_leq;
        destruct x as [t0 t1]; simpl;
        specialize (H0 t0); specialize (H t1);
        rewrite H0; rewrite H;
        reflexivity.

    Theorem top_prop L1 L2 : forall x, leq (L' (lat L1) (lat L2)) x (top (lat L1) (lat L2)) = true. topbot L1 L2 top_prop top. Qed.
    Theorem bot_prop L1 L2 : forall x, leq (L' (lat L1) (lat L2)) (bot (lat L1) (lat L2)) x = true. topbot L1 L2 bot_prop bot. Qed.

    Ltac prop1 L1 L2 which_prop1 :=
        intros x y; destruct x as [x1 x2], y as [y1 y2];

        (* surprisingly, it doesn't work with either of these (even though they worked interactively) *)
        (*specialize (which_prop1 L1) as H1; specialize (which_prop1 L2) as H2; *)
        (*specialize (which_prop1 L1); intro H1; specialize (which_prop1 L2); intro H2;*)
        (* it works with the following though *)
        specialize (which_prop1 L1); specialize (which_prop1 L2); intros H2 H1;

        specialize (H1 x1 y1); specialize (H2 x2 y2);
        simpl; unfold PRODUCT_POSET_M.product_leq; simpl;
        destruct H1 as [Ha Hb]; destruct H2 as [Hc Hd]; rewrite Ha, Hb, Hc, Hd;
        tauto.


    Theorem glb_prop1 L1 L2 : forall x y, leq (L' (lat L1) (lat L2)) (glb (lat L1) (lat L2) x y) x = true /\ leq (L' (lat L1) (lat L2)) (glb (lat L1) (lat L2) x y) y = true.  prop1 L1 L2 glb_prop1.  Qed.
    Theorem lub_prop1 L1 L2 : forall x y, leq (L' (lat L1) (lat L2)) x (lub (lat L1) (lat L2) x y) = true /\ leq (L' (lat L1) (lat L2)) y (lub (lat L1) (lat L2) x y) = true.  prop1 L1 L2 lub_prop1.  Qed.

    Ltac prop2 L1 L2 which_prop2 :=
        intros x y a H; destruct x as [x1 x2], y as [y1 y2], a as [a1 a2], H as [H3 H4];
        (*specialize (which_prop2 L1) as H1;  specialize (which_prop2 L2) as H2;*)
        specialize (which_prop2 L1);  specialize (which_prop2 L2); intros H2 H1;
        specialize (H1 x1 y1 a1); specialize (H2 x2 y2 a2);
        (apply PRODUCT_POSET_M.lift_leq in H3); (apply PRODUCT_POSET_M.lift_leq in H4);
        (*(destruct H3 as [Ha Hb]; destruct H4 as [Hc Hd]);  (simpl in Ha, Hb, Hc, Hd); *)
        (apply (PRODUCT_POSET_M.lift_leq' (L (lat L1)) (L (lat L2))));
        tauto.

    Theorem glb_prop2 L1 L2 : forall x y a, leq (L' (lat L1) (lat L2)) a x = true /\ leq (L' (lat L1) (lat L2)) a y = true -> leq (L' (lat L1) (lat L2)) a (glb (lat L1) (lat L2) x y) = true.  prop2 L1 L2 glb_prop2.  Qed.
    Theorem lub_prop2 L1 L2 : forall x y a, leq (L' (lat L1) (lat L2)) x a = true /\ leq (L' (lat L1) (lat L2)) y a = true -> leq (L' (lat L1) (lat L2)) (lub (lat L1) (lat L2) x y) a = true.  prop2 L1 L2 lub_prop2.  Qed.

End PRODUCT_LATTICE_M.

Definition PRODUCT_LATTICE (L1 L2 : LATTICE) : LATTICE := {|
    L := PRODUCT_POSET (L L1) (L L2);
    top := PRODUCT_LATTICE_M.top L1 L2; bot := PRODUCT_LATTICE_M.bot L1 L2;
    glb := PRODUCT_LATTICE_M.glb L1 L2; lub := PRODUCT_LATTICE_M.lub L1 L2;
    |}.

Program Definition PRODUCT_LATTICE_PROOFS (L1 L2 : LATTICE_PROOFS) : LATTICE_PROOFS := {|
    lat := PRODUCT_LATTICE (lat L1) (lat L2);
    pos := match (pos L1, pos L2) with (exist _ p1 e1, exist _ p2 e2) => exist _ (PRODUCT_POSET_PROOFS p1 p2) _ end;
    top_prop := PRODUCT_LATTICE_M.top_prop L1 L2; bot_prop := PRODUCT_LATTICE_M.bot_prop L1 L2;
    glb_prop1 := PRODUCT_LATTICE_M.glb_prop1 L1 L2; glb_prop2 := PRODUCT_LATTICE_M.glb_prop2 L1 L2;
    lub_prop1 := PRODUCT_LATTICE_M.lub_prop1 L1 L2; lub_prop2 := PRODUCT_LATTICE_M.lub_prop2 L1 L2;
    |}.
Next Obligation. rewrite e1; rewrite e2; reflexivity. Qed.

Variant FLAT_LATTICE_T {A : Set} {dec_eq : forall x y : A, {x = y} + {x <> y}} : Set := Bot : FLAT_LATTICE_T | Elem : A -> FLAT_LATTICE_T | Top : FLAT_LATTICE_T.
Module FLAT_LATTICE_M. Section FLAT_LATTICE_M.
    Variable A : Set.
    Variable dec_eq : forall x y : A, {x = y} + {x <> y}.
    Definition flat_lattice_leq (x y : FLAT_LATTICE_T (dec_eq := dec_eq) ) : bool := match (x, y) with
        | (Bot, _) => true
        | (_, Top) => true
        | (Elem x, Elem y) => sumbool_rec (fun _ => bool) (fun _ => true) (fun _ => false) (dec_eq x y)
        | _ => false
        end.

    Theorem dec_eq_refl : forall (x : A), {e : x = x | dec_eq x x = left e}.
        intros x; destruct (dec_eq x x) as [l | r] ; [refine (@exist (x = x) _ l _) | contradict r]; reflexivity.
    Qed.
    Theorem refl : forall (x : (@ FLAT_LATTICE_T A dec_eq)), flat_lattice_leq x x = true.
        intros x; destruct x as [|x|]; simpl; [| specialize (dec_eq_refl x) as H; destruct H as [x0 H0]; compute; rewrite H0 |]; reflexivity.
    Qed.
    Theorem antisym : forall (x y : (@ FLAT_LATTICE_T A dec_eq)), flat_lattice_leq x y = true -> flat_lattice_leq y x = true -> x = y.
        intros x y; destruct x as [| x |], y as [| y |]; compute; intros H H0; try reflexivity; match goal with
        | |- Elem _ = Elem _ => destruct dec_eq; [rewrite e; reflexivity | discriminate] (* this case distilled to `dec_eq_minimal_repro.v` *)
        | _ => discriminate
        end.
    Qed.
    Theorem trans : forall (x y z : (@ FLAT_LATTICE_T A dec_eq)), flat_lattice_leq x y = true -> flat_lattice_leq y z = true -> flat_lattice_leq x z = true.
        intros x y z Hxy Hyz.
        destruct x, y, z; compute; try reflexivity; try discriminate.
        compute in Hxy, Hyz; destruct (dec_eq a a0), (dec_eq a0 a1), (dec_eq a a1); try reflexivity; try discriminate.
        rewrite <- e in e0; destruct (n e0).
    Qed.

    Definition glb (x y : (@ FLAT_LATTICE_T A dec_eq)) :=
        match (x,y) with
        | (Bot, _) => Bot | (_, Bot) => Bot
        | (Elem x, Elem y) => sumbool_rec (fun _ => @ FLAT_LATTICE_T A dec_eq) (fun _ => Elem x) (fun _ => Bot) (dec_eq x y)
        | (Elem x, Top) => Elem x | (Top, Elem x) => Elem x
        | (Top, Top) => Top
        end.
    Definition lub (x y : (@ FLAT_LATTICE_T A dec_eq)) :=
        match (x,y) with
        | (Bot, Bot) => Bot
        | (Elem x, Bot) => Elem x | (Bot, Elem x) => Elem x
        | (Elem x, Elem y) => sumbool_rec (fun _ => @ FLAT_LATTICE_T A dec_eq) (fun _ => Elem x) (fun _ => Top) (dec_eq x y)
        | (Top, _) => Top | (_, Top) => Top
        end.
End FLAT_LATTICE_M. End FLAT_LATTICE_M.

Definition FLAT_LATTICE_POSET (A : Set) (dec_eq : forall x y : A, {x = y} + {x <> y}) : POSET := {|
    t := @ FLAT_LATTICE_T A dec_eq;
    leq := @ FLAT_LATTICE_M.flat_lattice_leq A dec_eq;
    |}.
Definition FLAT_LATTICE_POSET_PROOFS (A : Set) (dec_eq : forall x y : A, {x = y} + {x <> y}) : POSET_PROOFS := {|
    P := FLAT_LATTICE_POSET A dec_eq;
    refl := FLAT_LATTICE_M.refl A dec_eq;
    antisym := FLAT_LATTICE_M.antisym A dec_eq;
    trans := FLAT_LATTICE_M.trans A dec_eq;
    |}.
Definition FLAT_LATTICE_LATTICE (A : Set) (dec_eq : forall x y : A, {x = y} + {x <> y}) : LATTICE := {|
    L := FLAT_LATTICE_POSET A dec_eq;
    top := Top; bot := Bot;
    glb := FLAT_LATTICE_M.glb A dec_eq; lub := FLAT_LATTICE_M.lub A dec_eq;
    |}.

Scheme Equality for nat.
Definition nat_lat := FLAT_LATTICE_LATTICE nat nat_eq_dec.

Load ListBackedSet.

Definition wrap_exists {A B P} (f : A -> A -> B) := fun (x y : { z : A | P z }) => match (x, y) with (exist _ x _, exist _ y _) => f x y end.
Definition SUBSET_T A dec_eq (l : list A) := { x : list A | ListBackedSet.subset A dec_eq x l = true }.

Definition SET_POSET A dec_eq (ltop : list A) : POSET := {|
    t := SUBSET_T A dec_eq ltop;
    leq := wrap_exists (ListBackedSet.subset A dec_eq);
    |}.
(*
Program Definition SET_LATTICE A dec_eq (ltop : list A) : LATTICE := {|
    L := SET_POSET A dec_eq ltop;
    bot := exist _ nil _; top := exist _ ltop _;
    glb := _;
    lub := _;
    |}.
Next Obligation.
    simpl. induction ltop.
    - reflexivity.
    - simpl. unfold sumbool_rec. unfold sumbool_rect. destruct dec_eq. simpl.
*)
