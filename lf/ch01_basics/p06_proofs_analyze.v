(* Basics #lab39 to #lab44 *)

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

(* 
    Fixpoint eqb (n m : nat) : bool :=
    match n, m with
    | 0, 0       => true
    | 0, S _     => false
    | S _, 0     => false
    | S n1, S m1 => eqb n1 m1
    end.

    in second subgoal, it matches the third one and result is false
*)
Theorem plus_1_neq_0_firsttry : forall n : nat,
  ((n + 1) == 0) = false.
Proof.
    intros n.
    destruct n as [|myN] eqn:myEquation.
        - simpl. reflexivity.
        - simpl. reflexivity.
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

(* nested example which is not common *)
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
      (* with using {} we can use same bullet symbol otherwise we get => [Focus] Wrong bullet -: Current bullet - is not finished. *)
Qed.

Theorem andb3_exchange_better : forall b c d : bool, andb (andb b c) d = andb (andb b d) c.
Proof.
    intros b c d.
    destruct b, c, d;
    (* simpl. => just for checking them but it must have ; not . *) 
    reflexivity.
Qed.

(* =========== exercise: 2 stars, standard (andb_true_elim2) *)
Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
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

Theorem andb_true_elim2' : forall b c : bool, andb b c = true -> c = true.
Proof.
    intros b c H.
    destruct b, c.
        - reflexivity.
        - rewrite <- H. reflexivity.
        - reflexivity.
        - rewrite <- H. reflexivity.
Qed.

(* 
    a cleaner version of (intros + destruct) and that's because bool has a simple constructor 
*)
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
    intros [] [];
    reflexivity.
Qed.

(* =========== exercise: 1 star, standard (zero_nbeq_plus_1) *)
(*
    we write 1%nat to explicitly indicate that the literal 1
    should be interpreted in nat_scope and also the annotation n%bool is
    ignored because n is already declared as nat, thanks rocq
*)
Theorem zero_nbeq_plus_1 : forall n : nat, (0 == (n%bool + 1%nat)) = false.
Proof.
    intros [ | n' ];
    reflexivity.
Qed.

(* =========== exercise: 2 stars, standard, optional (decreasing) *)
(* Fixpoint bad_dec1 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => bad_dec1 (n' + 1)
end. *)

(* Fixpoint bad_dec2 (n : nat) : nat :=
match n with
    | O => 0
    | S n' => bad_dec2 (n' + 1)
end. *)
