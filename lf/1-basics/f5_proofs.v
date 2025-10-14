Example plus_1_1 : 1 + 1 = 2.
Proof. simpl. reflexivity. Qed.


(* ref does more than simpl.  *)
Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. reflexivity. Qed.


(* could be anything like m *)
Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof. intros m. reflexivity. Qed.

(* adding simpl will help to know how it is simplified *)
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.

(* _l means on the left *)
Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.


(* both -> and <- work here *)
Theorem plust_will_not_change_equality : forall n m : nat, n = m -> n + n = m + m.
Proof. intros n m J. rewrite <- J. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m ->
  m = o -> 
    n + m = m + o.
Proof.
    intros n m o H1 H2.
    rewrite H1, H2.
    reflexivity.
Qed.

