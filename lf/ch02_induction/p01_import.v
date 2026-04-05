(* Induction #lab61 to #lab66 *)

(* import thing *)
From SF Require Import lf.ch01_basics.p01_days.
Compute next_working_day chas.

(* n + 0 instead of 0 + n *)
Theorem add_0_r_try1 : forall n:nat, n + 0 = n.
Proof.
    intros n.
    simpl. (* does nothing! *)
Abort.

Theorem add_0_r_try2 : forall n:nat, n + 0 = n.
Proof.
    intros n. destruct n as [| n'] eqn:E.
        - (* n = 0 *) reflexivity.
        - (* n = S n' *) simpl. (* stuck again *)
Abort.

(* using induction *)
Theorem add_0_r_try3 : forall n:nat, n + 0 = n.
Proof.
    intros n.
    induction n as [|n' H].
        - reflexivity.
        - simpl. rewrite H. reflexivity.
Qed.

Theorem minus_n_n : forall n, n - n = 0.
Proof.
    intros n.
    induction n as [].
        - reflexivity.
        - simpl. rewrite IHn. reflexivity.
Qed.

(* =========== exercise: 2 stars, standard, especially useful (basic_induction) *)
Theorem mul_0_r : forall n:nat, n * 0 = 0.
Proof.
    intros n. induction n as [|n' H].
        - reflexivity.
        - simpl. rewrite H. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [|n' H].
        - reflexivity.
        - simpl. rewrite H. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
    intros n m.
    induction n, m.
        - reflexivity.
        - rewrite add_0_r_try3. reflexivity.
        - rewrite add_0_r_try3. reflexivity.
        - simpl. rewrite !IHn. simpl. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
    intros n m p.
    induction n.
        - reflexivity.
        - simpl. rewrite IHn. reflexivity.
Qed.

(* =========== exercise: 2 stars, standard (double_plus) *)
Fixpoint double (n:nat) :=
match n with
    | O => O
    | S n' => S (S (double n'))
end.

Lemma double_plus : forall n, double n = n + n .
Proof.
    intro n.
    induction n as [|n' H].
    - reflexivity.
    - simpl. rewrite H, plus_n_Sm. reflexivity.
Qed.

(* =========== exercise: 2 stars, standard, optional (even_S) *)
From SF Require Import lf.ch01_basics.p04_numbers. (* for even_recursive *)
From SF Require Import lf.ch01_basics.p06_proofs_analyze. (* for negb_involutive *)

Theorem even_S : forall n : nat, even_recursive (S n) = negb (even_recursive n).
Proof.
    intro n.
    induction n as [|n' H].
    - reflexivity.
    - rewrite H, negb_involutive. reflexivity.
Qed.


