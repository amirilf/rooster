(* Basics #lab35 to #lab38 *)

Example plus_1_1 : 1 + 1 = 2.
Proof. simpl. reflexivity. Qed.

(* ref does more than simpl.  *)
Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. reflexivity. Qed.

(* could be anything like m *)
Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof. intros m. reflexivity. Qed.

(*
  note that 0 + n = n is easy to prove but n + 0 = n is not like that
  since `add` is defined by recursion on first arg which is n:
      match n with
      | 0 => m
      | S n' => S (add n' m)
  then when the left side is 0, it immediately returns the right side.
  but when the right side is 0, we need to use induction on the left arg.
*)

(* adding simpl will help to know how it is simplified *)
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.

(* _l means on the left *)
Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.

(* both -> and <- work here *)
Theorem plus_will_not_change_equality : forall n m : nat, n = m -> n + n = m + m.
Proof. intros a b c. rewrite <- c. reflexivity. Qed.

(* =========== exercise: 1 star, standard (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
    n = m ->
    m = o -> 
    n + m = m + o.
Proof.
    intros n m o H1 H2.
    rewrite H1, H2.
    reflexivity.
Qed.

Check plus_id_exercise.
Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
    intros p q.
    rewrite <- mult_n_O, <- mult_n_O.
    reflexivity.
Qed.
(* we can also use !mult_n_0 which means do it for all occurrences *)

(* using replace *)
Theorem mult_n_0_m_0' : forall p q : nat,
    (p * 0) + (q * 0) = 0.
Proof.
    intros p q.
    replace (q * 0) with 0 by apply mult_n_O.
    replace (p * 0) with 0 by apply mult_n_O.
    reflexivity.
Qed.

(* 
    using pattern to be able to match specific part 
    it only applies to the next tactic not all of em
    so this is why the second replace line will replace all
    of the remaining (q * 0) ones.
*)
Theorem mult_n_0_m_0'' : forall p q : nat,
    (q * 0) + (p * 0) + (q * 0) + 1 +  (q * 0) + 2 + (q * 0) = 3.
Proof.
    intros p q.
    pattern (q * 0) at 3.
    replace (q * 0) with 0 by apply mult_n_O. (* the third one *)
    replace (q * 0) with 0 by apply mult_n_O. (* other ones *)
    replace (p * 0) with 0 by apply mult_n_O.
    reflexivity.
Qed.

(* =========== exercise: 1 star, standard (mult_n_1) *)
Theorem mult_n_1 : forall p : nat, 
    p * 1 = p.
Proof.
    intros p.
    rewrite <- mult_n_Sm. (* n * m + n = n * 1 + m  => here m = 0 *)
    rewrite <- mult_n_O.
    reflexivity.
Qed.
