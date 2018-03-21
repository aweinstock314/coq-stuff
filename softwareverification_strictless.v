Record StrictLess := {
    sl : nat -> nat -> bool;
    sl_z_s : forall n, sl 0 (S n) = true;
    sl_not_zero : forall n, ~(sl n 0 = true);
    sl_inj : forall n m, sl (S n) (S m) = true <-> sl n m = true
    }.

(*
definitions from Print:

Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m

lt = fun n m : nat => S n <= m
     : nat -> nat -> Prop
*)

Lemma lt_not_zero : forall n, ~(lt n 0).
    intros n Hle. inversion Hle. Qed.

Lemma le_0_n' : forall n, 0 <= n.
    induction n.
    - apply le_n.
    - apply le_S. exact IHn.
    Qed.

Lemma le_inj_rl : forall n m, (S n) <= (S m) -> n <= m.
    intros n m Hle.
    induction m; inversion Hle; try apply le_n.
     - inversion H0.
     - apply le_S. exact (IHm H0).
    Qed.

Lemma le_inj_lr : forall n m, n <= m -> (S n) <= (S m).
    intros n m Hle.
    induction m; inversion Hle; try apply le_n.
    auto.
    Qed.

Fixpoint le_dec (n m : nat) : {le n m} + {~le n m} :=
    match m with
    | 0 => match n with
        | 0 => left (le_n 0)
        | S n' => right (lt_not_zero _)
        end
    | S m' => match n with
        | 0 => match le_dec 0 m' with
            | left wit => left (@ le_S _ _ wit)
            | right wit => right (match wit (le_0_n' _) with end)
            end
        | S n' => match le_dec n' m' with
            | left wit => left (le_inj_lr _ _ wit)
            | right wit => right (fun (H : le (S n') (S m')) => wit (le_inj_rl _ _ H))
            end
        end
    end.

Lemma lift_le_dec : forall (n m : nat), n <= m -> (if le_dec n m then true else false) = true.
    intros n m Hle. destruct (le_dec n m) as [_ | Hnle]; [ reflexivity | exfalso; exact (Hnle Hle) ].
    Qed.
Lemma lower_le_dec : forall (n m : nat), (if le_dec n m then true else false) = true -> n <= m.
    intros n m Hle_dec. destruct le_dec as [Hle | Hnle]; [exact Hle | discriminate Hle_dec].
    Qed.

Definition StrictLess_Inst := {|
    sl := fun n m => if le_dec (S n) m then true else false;
    sl_z_s := fun n => lift_le_dec _ _ (le_inj_lr _ _ (le_0_n' n));
    sl_not_zero := fun n e => lt_not_zero n (lower_le_dec (S n) 0 e);
    sl_inj := fun n m => conj
        (fun H => lift_le_dec _ _ (le_inj_rl _ _ (lower_le_dec _ _ H)))
        (fun H => lift_le_dec _ _ (le_inj_lr _ _ (lower_le_dec _ _ H)));
    |}.
