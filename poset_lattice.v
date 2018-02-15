Require Import Coq.Program.Tactics.

Record POSET : Type := mkPoset {
    t : Type;
    leq : t -> t -> bool;
    }.
Record POSET_PROOFS : Type := mkPosetProofs {
    P : POSET;
    refl : forall x, leq P x x = true;
    antisym : forall x y, leq P x y = true /\ leq P y x = true -> x = y;
    trans : forall x y z, leq P x y = true /\ leq P y z = true -> leq P x z = true;
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
    Definition to (p : POSET') : POSET := {| t := t' p; leq := to_leq p |}.

    Theorem orig_refl (p : POSET') : forall x, {e : x = x | pcomp p x x = Equal e}.
        intro x. destruct (pcomp p x x); try contradiction. exists e. reflexivity. Qed.
    Theorem to_refl (p : POSET') : forall x, leq (to p) x x = true.
        intro x; simpl; unfold to_leq; destruct (pcomp p x x); try contradiction; reflexivity. Qed.
    Theorem to_antisym (p : POSET') : forall x y, leq (to p) x y = true /\ leq (to p) y x = true -> x = y.
        intros x y; simpl; unfold to_leq.
        specialize (trans_l p x y x) as trans_l_instance.
        destruct (pcomp p x y), (pcomp p y x); (* 4*4 = 16 cases to handle *)
            try [> intro H; destruct H; discriminate]; (* all 12 cases involving Greater/Uncomparable follow vacuously *)
            try [> intro; try exact e; exact (eq_sym e)]. (* all 3 remaining cases involving an equality are resolved from the witness *)
        (* in the Less/Less case, x < y & y < x, leading (by trans_l) x < x, which violates reflexivity *)
        destruct (trans_l_instance (exist _ n eq_refl) (exist _ n0 eq_refl)); contradiction.
        Qed.
    Theorem to_trans (p : POSET') : forall x y z, leq (to p) x y = true /\ leq (to p) y z = true -> leq (to p) x z = true.
        intros x y z; simpl; unfold to_leq.
        specialize (trans_l p x y z) as trans_l_instance.
        destruct (pcomp p x y) eqn:Hxy, (pcomp p y z)eqn:Hyz;
            try [> intros; destruct H; discriminate]; (* handle the trivially vacuous cases *)
            try [> intros; reflexivity]; (* handle the remaining equality cases *)
            match goal with
            | _:pcomp p x y = Less _, _:pcomp p y z = Less _ |- _ => destruct (trans_l_instance (exist _ n eq_refl) (exist _ n0 eq_refl)); try discriminate; (rewrite e; reflexivity)
            | exy:x=y, eyz:y=z, nxz:x<>z |- _  => destruct (nxz (eq_trans exy eyz))
            | e:_=_, H:pcomp _ _ _ = Less _ |- _ => subst; rewrite H; reflexivity
            | exy:x=y, eyz:y=z |- _ => rewrite (eq_trans exy eyz); destruct (orig_refl p z) as [x' e']; rewrite e'; reflexivity
        end. Qed.
    Definition to' (p : POSET') : POSET_PROOFS := {| P := to p; refl := to_refl p; antisym := to_antisym p; trans := to_trans p |}.

    Theorem leq_false_neq (p : POSET_PROOFS) : forall x y, leq (P p) x y = false -> x <> y.
        intros x y Hleq exy; rewrite exy, (refl p y) in Hleq; discriminate. Qed.
    Definition neq_sym {A : Type} {x y : A} (n : x <> y) : (y <> x) := fun e => n (eq_sym e).
    (*Definition from_leq (p : POSET_PROOFS) : forall x y, @Pord (t (P p)) x y := fun x y =>
        let lxy := leq (P p) x y in let lyx := leq (P p) y x in
        match lxy as bxy return (lxy = bxy) -> Pord with
            | true => fun exy => match lyx as byx return (lyx = byx) -> Pord with
                | true => fun eyx => Equal (antisym p x y (conj exy eyx))
                | false => fun eyx => Less (neq_sym (leq_false_neq p y x eyx))
            end eq_refl | false => fun exy => match lyx with
                | true => Greater (leq_false_neq p x y exy)
                | false => Uncomparable (leq_false_neq p x y exy)
            end
        end eq_refl.*)
    Definition or_intro1 {P Q R S : Prop} (x : P) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition or_intro2 {P Q R S : Prop} (x : Q) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition or_intro3 {P Q R S : Prop} (x : R) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition or_intro4 {P Q R S : Prop} (x : S) : P \/ Q \/ R \/ S := ltac:(tauto).
    Definition from_leq' (p : POSET_PROOFS) : forall x y, { r : @Pord (t (P p)) x y |
        {e : x = y | r = Equal e /\ (leq (P p) x y, leq (P p) y x) = (true, true)} \/
        {n : x <> y | r = Less n /\ (leq (P p) x y, leq (P p) y x) = (true, false)} \/
        {n : x <> y | r = Greater n /\ (leq (P p) x y, leq (P p) y x) = (false, true)} \/
        {n : x <> y | r = Uncomparable n /\ (leq (P p) x y, leq (P p) y x) = (false, false)}} :=
        fun x y => let leqs := (leq (P p) x y, leq (P p) y x) in
        match leqs as bools return (leqs = bools) -> _ with
            | (true, true) => fun e => let e' := (antisym p x y (conj (f_equal fst e) (f_equal snd e))) in
                exist _ (Equal e') (or_intro1 (exist _ e' (conj eq_refl e)))
            | (true, false) => fun e => let n := (neq_sym (leq_false_neq p y x (f_equal snd e))) in
                exist _ (Less n) (or_intro2 (exist _ n (conj eq_refl e)))
            | (false, true) => fun e => let n := (leq_false_neq p x y (f_equal fst e)) in
                exist _ (Greater n) (or_intro3 (exist _ n (conj eq_refl e)))
            | (false, false) => fun e => let n := (leq_false_neq p x y (f_equal fst e)) in
                exist _ (Uncomparable n) (or_intro4 (exist _ n (conj eq_refl e)))
        end eq_refl.
    Definition from_leq (p : POSET_PROOFS) : forall x y, @Pord (t (P p)) x y := fun x y => match from_leq' p x y with exist _ ord _ => ord end.
    Theorem leq_implies_from_leq (p : POSET_PROOFS) : forall x y, leq (P p) x y = true -> { n | from_leq p x y = Less n } \/ { e | from_leq p x y = Equal e }.
        intros x y Hleq. remember (from_leq p x y) as result eqn:foo1.
        unfold from_leq in foo1.
        destruct (from_leq' p x y) eqn:foo2; decompose [or] o.
        - destruct H. right. exists x1. rewrite <- foo1 in a. exact (proj1 a).
        - destruct H0. left. exists x1. rewrite <- foo1 in a. exact (proj1 a).
        - destruct H. destruct a. remember (f_equal fst H0). simpl in e. rewrite e in Hleq. discriminate Hleq.
        - destruct H. destruct a. remember (f_equal fst H0). simpl in e. rewrite e in Hleq. discriminate Hleq.
        Qed.
    (*Theorem from_trans (p : POSET_PROOFS) : forall x y z, { nxy | from_leq p x y = Less nxy} -> {nyz | from_leq p y z = Less nyz } -> { nxz | from_leq p x z = Less nxz }.
        intros x y z Hxy Hyz. destruct Hxy as [nxy lxy], Hyz as [nyz lyz].
        specialize (trans p x y z) as tr.
        destruct (leq (P p) x y) eqn:foo; destruct (leq (P p) y z) eqn:bar.*)
    (*Definition from : (p : POSET_PROOFS) : POSET' := *)
End POSET_ISOMORPHISMS.

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
    Theorem antisym (P1 P2 : POSET_PROOFS) : forall x y, product_leq (P P1) (P P2) x y = true /\ product_leq (P P1) (P P2) y x = true -> x = y.
        intros; destruct x,y.
        cut (t0=t2 /\ t1=t3). intro H0; destruct H0; rewrite H0; rewrite H1; reflexivity.
        specialize (antisym P1 t0 t2). specialize (antisym P2 t1 t3). intros.
        (destruct H). (apply (lift_leq (P P1) (P P2)) in H; simpl in H). (apply (lift_leq (P P1) (P P2)) in H2; simpl in H2).
        tauto.
    Qed.

    Theorem trans (P1 P2 : POSET_PROOFS) : forall x y z, product_leq (P P1) (P P2) x y = true /\ product_leq (P P1) (P P2) y z = true -> product_leq (P P1) (P P2) x z = true.
        intros **. (destruct x, y, z).
        specialize (trans P1 t0 t2 t4). specialize (trans P2 t1 t3 t5). intros **.
        destruct H.
        unfold product_leq; simpl.
        (apply lift_leq in H). (apply lift_leq in H2).
        (simpl in H, H2). (destruct H, H2).
        (rewrite H, H2 in H1). (rewrite H3, H4 in H0).
        (destruct H0). tauto. (destruct H1). tauto.
        (destruct (leq (P P1) t0 t4); tauto).
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
Module FLAT_LATTICE_M.
    Definition flat_lattice_leq {A : Set} {dec_eq : forall x y : A, {x = y} + {x <> y}} (x y : FLAT_LATTICE_T (dec_eq := dec_eq) ) : bool := match (x, y) with
        | (Bot, _) => true
        | (_, Top) => true
        | (Elem x, Elem y) => sumbool_rec (fun _ => bool) (fun _ => true) (fun _ => false) (dec_eq x y)
        | _ => false
        end.

    Theorem dec_eq_refl : forall (A : Type) (dec_eq : forall x y : A, {x = y} + {x <> y}) (x : A), {e : x = x | dec_eq x x = left e}.
        intros A dec_eq x; destruct (dec_eq x x) as [l | r] ; [refine (@exist (x = x) _ l _) | contradict r]; reflexivity.
    Qed.
    Theorem refl : forall A dec_eq (x : (@ FLAT_LATTICE_T A dec_eq)), flat_lattice_leq x x = true.
        intros A dec_eq x; destruct x as [|x|]; simpl; [| specialize (dec_eq_refl A dec_eq x) as H; destruct H as [x0 H0]; compute; rewrite H0 |]; reflexivity.
    Qed.
    Theorem antisym : forall A dec_eq (x y : (@ FLAT_LATTICE_T A dec_eq)), flat_lattice_leq x y = true /\ flat_lattice_leq y x = true -> x = y.
        intros A dec_eq x y; destruct x as [| x |], y as [| y |]; compute; intro H; try reflexivity; match goal with
        | |- Elem _ = Elem _ => destruct dec_eq; [rewrite e; reflexivity | discriminate (proj1 H)] (* this case distilled to `dec_eq_minimal_repro.v` *)
        | _ => destruct H; discriminate
        end.
    Qed.
    Theorem trans : forall A dec_eq (x y z : (@ FLAT_LATTICE_T A dec_eq)), flat_lattice_leq x y = true /\ flat_lattice_leq y z = true -> @ flat_lattice_leq A dec_eq x z = true.
        intros A dec_eq x y z H. destruct H as [Hxy Hyz].
        destruct x, y, z; compute; try reflexivity; try discriminate.
        compute in Hxy, Hyz; destruct (dec_eq a a0), (dec_eq a0 a1), (dec_eq a a1); try reflexivity; try discriminate.
        rewrite <- e in e0; destruct (n e0).
    Qed.

    Definition glb A dec_eq (x y : (@ FLAT_LATTICE_T A dec_eq)) :=
        match (x,y) with
        | (Bot, _) => Bot | (_, Bot) => Bot
        | (Elem x, Elem y) => sumbool_rec (fun _ => @ FLAT_LATTICE_T A dec_eq) (fun _ => Elem x) (fun _ => Bot) (dec_eq x y)
        | (Elem x, Top) => Elem x | (Top, Elem x) => Elem x
        | (Top, Top) => Top
        end.
    Definition lub A dec_eq (x y : (@ FLAT_LATTICE_T A dec_eq)) :=
        match (x,y) with
        | (Bot, Bot) => Bot
        | (Elem x, Bot) => Elem x | (Bot, Elem x) => Elem x
        | (Elem x, Elem y) => sumbool_rec (fun _ => @ FLAT_LATTICE_T A dec_eq) (fun _ => Elem x) (fun _ => Top) (dec_eq x y)
        | (Top, _) => Top | (_, Top) => Top
        end.
End FLAT_LATTICE_M.

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

Module LISTSET_M.
    (*Parameter A : Type.
    Parameter dec_eq : forall x y : A, {x = y} + {x <> y}.*)
    Fixpoint elem (A : Type) (dec_eq : forall x y : A, {x = y} + {x <> y}) x l : bool :=
        match l with nil => false | cons y ys => orb (sumbool_rec (fun _ => bool) (fun _ => true) (fun _ => false) (dec_eq x y)) (elem A dec_eq x ys) end.
    Fixpoint subset A dec_eq l1 l2 : bool :=
        match l1 with nil => true | cons y ys => andb (elem A dec_eq y l2) (subset A dec_eq ys l2) end.
    Definition eqset A dec_eq l1 l2 : bool := andb (subset A dec_eq l1 l2) (subset A dec_eq l2 l1).
    Fixpoint map {A B : Type} (f : A -> B) (l : list A) := match l with nil => nil | cons x xs => cons (f x) (map f xs) end.
    Fixpoint powerset {A} (l : list A) : list (list A) := match l with nil => (cons nil nil) | cons x xs => app (powerset xs) (map (cons x) (powerset xs)) end.

    Fixpoint expnat b e := match e with 0 => 1 | S e' => b * expnat b e' end.

    Ltac simple_nat_induction n c1 c2 := intros; induction n as [ | n IHn ]; simpl; [ c1 | rewrite IHn; c2 ]; reflexivity.
    Ltac simple_list_induction n c1 c2 := intros; induction n as [ | x xs IHxs ]; simpl; [ c1 | c2; rewrite IHxs ]; reflexivity.

    Theorem length_app_plus : forall A (xs ys : list A), length (app xs ys) = length xs + length ys. simple_list_induction xs idtac idtac. Qed.
    Theorem plus_rightid : forall n, n + 0 = n. simple_nat_induction n idtac idtac. Qed.
    Theorem plus_double : forall n, n + n = 2 * n.  intros n; induction n; simpl; [|rewrite plus_rightid]; reflexivity. Qed.
    Theorem length_map : forall (A B : Type) (f : A -> B) xs, length xs = length (map f xs). simple_list_induction xs idtac idtac. Qed.

    Theorem powerset_length : forall (A : Type) (l : list A), length (powerset l) = expnat 2 (length l).
        simple_list_induction l idtac ltac:(rewrite length_app_plus, plus_rightid, <- (@ length_map (list A) (list A) (cons x))).
    Qed.

    Definition union := app.
    Fixpoint intersection A dec_eq l1 l2 := match l1 with
        | nil => nil
        | cons x xs => (if elem A dec_eq x l2 then cons x else (fun a => a)) (intersection A dec_eq xs l2)
        end.

    Theorem subset_nil : forall A dec_eq (x : list A), subset A dec_eq x nil = true -> x = nil.
        (intros ** ). (induction x). reflexivity. (compute in H). discriminate H. Qed.
    Theorem subset_antisym : forall A dec_eq (x y : list A), subset A dec_eq x y = true /\ subset A dec_eq y x = true -> eqset A dec_eq x y = true.
        intros. (simpl). (unfold eqset). (destruct H). (rewrite H, H0). (simpl). reflexivity. Qed.
    Theorem elem_liftbool : forall A dec_eq (a b : A) (x : list A), elem A dec_eq a (b :: x)%list = true -> (a = b \/ (a <> b /\ elem A dec_eq a x = true)).
        intros A dec_eq a b x H; inversion H; destruct dec_eq as [e | n]; [ exact (or_introl e) | right; (unfold sumbool_rec, sumbool_rect); exact (conj n eq_refl)]. Qed.
    Theorem elem_cons_eq : forall A dec_eq (a b : A) (x : list A), a = b -> elem A dec_eq a (b :: x)%list = true.
        intros A dec_eq a b x e; rewrite e; compute; destruct (dec_eq b b); [|contradict n]; reflexivity. Qed.
    Theorem elem_cons_neq : forall A dec_eq (a b : A) (x : list A), a <> b -> elem A dec_eq a (b :: x)%list = elem A dec_eq a x.
        intros A dec_eq a b x n; simpl; unfold sumbool_rec, sumbool_rect; destruct dec_eq as [e|_]; [exact match n e with end | reflexivity]. Qed.
    Theorem elem_cons_extend : forall A dec_eq (a b : A) (xs : list A), elem A dec_eq a xs = true -> elem A dec_eq a (b :: xs) = true.
        intros A dec_eq a b xs a_in_xs; destruct (dec_eq a b); [exact (elem_cons_eq A _ a b xs e) | rewrite (elem_cons_neq A _ a b xs n); exact a_in_xs]. Qed.
    (*Theorem subset_lcons : forall A dec_eq (a : A) (x y : list A), subset A dec_eq (a :: x) y = true -> subset A dec_eq x y = true.
(intros A dec_eq a x y H). (induction x).
    - reflexivity.
    -*)
    (*Theorem subset_rcons : forall A dec_eq (a : A) (x y : list A), subset A dec_eq x (a :: y) = true -> elem A dec_eq a x = true \/ subset A dec_eq x y = true.
        intros A dec_eq a x y H. induction x.
        - simpl. tauto.
        - simpl. unfold sumbool_rec. unfold sumbool_rect. destruct dec_eq.
            + simpl. tauto.
            + simpl.*)
    (*Theorem subset_constail : forall A dec_eq (a : A) (x y : list A), subset A dec_eq x y = true -> subset A dec_eq x (a :: y) = true.
        intros A dec_eq a x y H.*)
    (*Theorem subset_refl : forall A dec_eq (x : list A), subset A dec_eq x x = true.
    intros A dec_eq x. induction x .
    - reflexivity.
    - simpl. unfold sumbool_rec. unfold sumbool_rect. destruct dec_eq.
        + simpl.
    *)
    (*Theorem subset_trans : forall A dec_eq (x y z : list A), subset A dec_eq x y = true /\ subset A dec_eq y z = true -> subset A dec_eq x z = true.
        (intros ** ).  (destruct H).  (induction y).
        - (rewrite (subset_nil A dec_eq x H)).  (apply H0).
        - 
    *)

End LISTSET_M.

Definition wrap_exists {A B P} (f : A -> A -> B) := fun (x y : { z : A | P z }) => match (x, y) with (exist _ x _, exist _ y _) => f x y end.
Definition SUBSET_T A dec_eq (l : list A) := { x : list A | LISTSET_M.subset A dec_eq x l = true }.

Definition SET_POSET A dec_eq (ltop : list A) : POSET := {|
    t := SUBSET_T A dec_eq ltop;
    leq := wrap_exists (LISTSET_M.subset A dec_eq);
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
