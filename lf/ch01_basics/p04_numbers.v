Module MyModule.
    Inductive nat' : Type :=
        | O
        | S (n : nat').

    Definition sub_1 (n : nat') : nat' :=
        match n with
            | O => O
            | S n' => n'
        end.

    Definition add_1 (n : nat') : nat' :=
        match n with
            | O => S O
            | S n' => S (S n')
        end.

    Definition better_add_1 (n : nat') : nat' :=
        S n.

    Compute sub_1 (S (S (S (S O)))).
    Compute add_1 (S (S (S (S O)))).
    Compute add_1 (S (S O)).
    Compute better_add_1 (S (S (S (S O)))).
    Compute better_add_1 (S (S O)).

    Check (S (S (S (S O)))).

End MyModule.

(* ============= built in ones*)

Check (S (S (S (S O)))).

Definition sub_2 (n : nat) : nat :=
    match n with
        | O => O
        | S O => O
        | S (S n') => n'
    end.

Definition test_number : nat := (S (S (S (S (S O))))).
Compute test_number.
Compute sub_2 test_number.

Check sub_2.
Check O.
Check S.

(* ============ recursive *)

Fixpoint devidable_by_3 (n : nat) : bool :=
    match n with
        | O => true
        | S O => false
        | S (S O) => false
        | S (S (S n')) => devidable_by_3 n'
    end.

Definition n0  : nat := 0.
Definition n1  : nat := 1.
Definition n2  : nat := 2.
Definition n3  : nat := 3.
Definition n4  : nat := 4.

Compute devidable_by_3 n0.
Compute devidable_by_3 n1.
Compute devidable_by_3 n2.
Compute devidable_by_3 n3.
Compute devidable_by_3 n4.
Compute devidable_by_3 (S (S (S (S (S O))))). (* 5 *)
Compute devidable_by_3 (S (S (S (S (S(S O)))))). (* 6 *)

(* =========== *)

Fixpoint even_recursive (n : nat) : bool :=
    match n with
        | O => true
        | S O => false
        | S (S n') => even_recursive n'
    end.

Definition odd_direct (n:nat) : bool :=
  negb (even_recursive n).

Example test_even_recursive1: even_recursive 1 = false.
Proof. simpl. reflexivity. Qed.

Example test_even_recursive2: even_recursive 4 = true.
Proof. simpl. reflexivity. Qed.

(* ============= multi param funcs *)

Fixpoint add (a b : nat) : nat :=
    match a with
        | O => b
        | S a' => S (add a' b)
    end.

Compute add 3 3.
Compute add 21 10.
Compute add 3234 3.
Compute add (S (S (S O))) (S O).


Fixpoint sub (a b : nat) : nat :=
    match b with
        | O => a
        | S b' => 
            match a with
                | O => O
                | S a' => sub a' b'
            end
    end.

Compute sub 6 6.
Compute sub 6 7.
Compute sub 6 8.
Compute sub 7 6.
Compute sub 31 3.
Compute sub 17 0.


Fixpoint sub_better (a b : nat) : nat :=
    match a, b with
        | O, _ => O
        | _, O => a
        | S n', S m' => sub_better n' m'
    end.

Compute sub_better 6 6.
Compute sub_better 6 7.
Compute sub_better 6 8.
Compute sub_better 7 6.
Compute sub_better 31 3.
Compute sub_better 17 0.

Fixpoint mul (a b : nat) : nat :=
    match b with
        | O => O
        | S b' => add a (mul a b')
    end.

Compute mul 2 3.
Compute mul 10 3.
Compute mul 21 4.
Compute mul 5 17.

Fixpoint expo (a b : nat) : nat :=
    match b with
        | O => S O
        | S b' => mul a (expo a b')
    end.

Compute expo 0 0.
Compute expo 2 3.
Compute expo 3 4.
Compute expo 10 4.

(* =========== EX3 * factorial *)

Fixpoint factorial (n:nat) : nat :=
    match n with
        | O => O
        | S O => n
        | S n' => mul n (factorial n')
    end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mul 10 12).
Proof. simpl. reflexivity. Qed.


(* ============ notations for em *)

Notation "x + y" := (add x y) (at level 50, left associativity).
Notation "x - y" := (sub_better x y) (at level 50, left associativity).
Notation "x * y" := (mul x y) (at level 40, left associativity).

Check ((0 + 1) + 1) : nat.
Compute 10 + 23 * 2.

(* =========== equality *)

Fixpoint equal (a b : nat) : bool :=
    match a,b with
        | O, O => true
        | O, _ => false
        | _, O => false
        | S a', S b' => equal a' b'
    end.

Notation "x = y" := (equal x y).

Compute (0 = 0).
Compute (0 = 1).
Compute (2 = 0).
Compute (10 = 11).
Compute (22 = 22).

(* ========= a <= b *)

Definition less_or_equal (a b : nat) : bool :=
    equal (sub a b) O.

Notation "x <=? y" := (less_or_equal x y) (at level 70).

Compute 1 <=? 10.
Compute 10 <=? 1.
Compute 1 <=? 1.

(* ========= a >= b *)
Definition more_or_equal (a b : nat) : bool :=
    equal (sub b a) O.

Notation "x >=? y" := (more_or_equal x y) (at level 70).

Compute 1 >=? 10.
Compute 10 >=? 1.
Compute 1 >=? 1.

(* =========== EX4 * less than *)

Definition less_than (a b : nat) : bool :=
    negb (more_or_equal a b).
    
Notation "x <? y" := (less_than x y) (at level 70).

Compute 1 <? 2.
Compute 2 <? 1.
Compute 1 <? 1.

Example test_ltb1: (less_than 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (less_than 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (less_than 4 2) = false.
Proof. simpl. reflexivity. Qed.

