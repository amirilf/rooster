Fixpoint sub (a b : nat) : nat :=
    match a, b with
        | O, _ => O
        | _, O => a
        | S a', S b' => sub a' b'
    end.

Definition equal (a b : nat) : bool :=
    match sub a b, sub b a with
        | O, O => true
        | _, _ => false
    end.

Notation "x == y" := (equal x y) (at level 70).

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) == 0 = false.
Proof.
    intros n.
    destruct n as [|n'] eqn:myEquation.
        - reflexivity.
        - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b.
    destruct b.
    - 
        simpl. (* to see how it is simplified *)
        reflexivity.
    - reflexivity.
Qed.

(* we can use nested destructs for all possible scenarios *)
Theorem andb_commutative : forall b c : bool, andb b c = andb c b.
Proof.
    intros b c. 
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn:Ec.
        { 
            reflexivity.
        } {
            reflexivity.
        }
Qed.


Theorem andb3_exchange : forall b c d : bool, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

(* =========== EX7 ** andb_true_elim2 *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
    intros b c H.
    destruct b eqn:Eb.
        - destruct c eqn:Ec.    
            + reflexivity. 
            + rewrite <- H. reflexivity.
        - destruct c eqn:Ec.
            + reflexivity.
            + rewrite <- H. reflexivity.
Qed.


(* 
    a cleaner version of (intros + destruct) 
    note that we lose eqn:E in this style
*)
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
    intros [] [].
        - reflexivity.  (* ff *)
        - reflexivity.  (* ft *)
        - reflexivity.  (* tf *)
        - reflexivity.  (* tt *)
Qed.

(* =========== EX8 * zero_nbeq_plus_1 *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 == (n + 1) = false.
Proof.
    intros [|n'].
        - reflexivity.
        - reflexivity.
Qed.

(* =========== EX9 ** decreasing *)
Fixpoint my_valid_decreasing_func_but_idiot_coq (a b : nat) : nat :=
    match a,b with
        | _, O => a
        | _, _ => my_valid_fun_but_idiot_coq (a+1) (b-1)
    end.

Compute my_valid_fun_but_idiot_coq 10 3.
