(* Basics #lab45 to #lab59 *)

(* =========== exercise: 1 star, standard (identity_fn_applied_twice) *)
Theorem identity_fn_applied_twice :
    forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
    intros f H x.
    rewrite H, H. (* or !H *)
    reflexivity.
Qed.

(* =========== exercise: 1 star, standard (negation_fn_applied_twice) *)
Theorem neg_of_neg : forall b : bool, negb (negb b) = b.
Proof.
    intros [];
    reflexivity.
Qed.

Theorem negation_fn_applied_twice :
    forall (f : bool -> bool), (forall (x : bool), f x = negb x) 
    -> forall (b : bool), f (f b) = b.
Proof.
    intros f H x.
    rewrite !H, neg_of_neg.
    reflexivity.
Qed.

(* some random things *)
Theorem a_is_orb_when_true : 
    forall a b : bool, a = true -> orb a b = true.
Proof.
    intros a b H.
    rewrite H.
    reflexivity.
Qed.

Theorem a_is_andb_when_false : forall a b : bool, a = false -> andb a b = false.
Proof.
    intros a b H.
    rewrite H.
    reflexivity.
Qed.

Theorem a_is_andb_with_true : forall a : bool, andb true a = a.
Proof.
    reflexivity.
Qed.

Theorem a_is_orb_with_false : forall a : bool, orb false a = a.
Proof.
    reflexivity.
Qed.

(* =========== exercise: 3 stars, standard, optional (andb_eq_orb) *)
Theorem andb_eq_orb1 : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
    intros [] [].
        - reflexivity.
        - discriminate.
        - discriminate.
        - reflexivity.
Qed.

Theorem andb_eq_orb2 : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
    intros a b H.
    destruct a as [] eqn:Ea;
    simpl in H; rewrite H; 
    reflexivity.
Qed.

Theorem andb_eq_orb3 : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
    intros a b.
    destruct a;
    simpl; 
    intros H; 
    rewrite H; 
    reflexivity.
Qed.

Theorem andb_eq_orb4 : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
    intros [] [] H; reflexivity || discriminate.
Qed.

(* ============ course late policies *)

Module LateDays.

Inductive letter : Type := 
    | A
    | B
    | C
    | D
    | F.

Inductive modifier : Type :=
    | Plus
    | Natural
    | Minus.

Inductive grade : Type := Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
    | Eq (* "equal" *)
    | Lt (* "less than" *)
    | Gt. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
    match l1, l2 with
        | A, A => Eq
        | A, _ => Gt
        | B, A => Lt
        | B, B => Eq
        | B, _ => Gt
        | C, (A | B) => Lt
        | C, C => Eq
        | C, _ => Gt
        | D, (A | B | C) => Lt
        | D, D => Eq
        | D, _ => Gt
        | F, (A | B | C | D) => Lt
        | F, F => Eq
    end.

Compute letter_comparison B A.
Compute letter_comparison D D.
Compute letter_comparison B F.


(* =========== exercise: 1 star, standard (letter_comparison) *)
Theorem letter_comparison_Eq : forall l, letter_comparison l l = Eq.
Proof.
    intros [];
    reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
    match m1, m2 with
        | Plus, Plus => Eq
        | Plus, _ => Gt
        | Natural, Plus => Lt
        | Natural, Natural => Eq
        | Natural, _ => Gt
        | Minus, (Plus | Natural) => Lt
        | Minus, Minus => Eq
    end.

(* =========== exercise: 2 stars, standard (grade_comparison) *)
Definition grade_comparison (g1 g2 : grade) : comparison :=
    match g1, g2 with Grade l1 m1, Grade l2 m2 =>
        match letter_comparison l1 l2 with
            | Eq => modifier_comparison m1 m2
            | anyother => anyother
        end
    end.

Example test_grade_comparison1 : (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 : (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. reflexivity. Qed.
Example test_grade_comparison3 : (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. reflexivity. Qed.
Example test_grade_comparison4 : (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. reflexivity. Qed.


Definition lower_letter (l : letter) : letter :=
    match l with
        | A => B
        | B => C
        | C => D
        | D => F
        | F => F
    end.

Theorem lower_letter_lowers: forall (l : letter),
    letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. (* I'm stuck son *)
Abort.

Theorem lower_letter_F_is_F: lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

(* =========== exercise: 2 stars, standard (lower_letter_lowers) *)
Theorem lower_letter_lowers: 
    forall (l : letter), 
        letter_comparison F l = Lt -> 
        letter_comparison (lower_letter l) l = Lt.
Proof.
    intros l H;
    destruct l;
    rewrite <- H;
    reflexivity.
Qed.

Theorem lower_letter_lowers2:
    forall (l : letter),
        letter_comparison F l = Lt ->
        letter_comparison (lower_letter l) l = Lt.
Proof.
    intros l H.
    destruct l;
    simpl;
    reflexivity || discriminate H.
Qed.

(* =========== exercise: 2 stars, standard (lower_grade) *)
Definition lower_grade (g : grade) : grade :=
    match g with Grade l m =>
        match m with
            | Plus => Grade l Natural
            | Natural => Grade l Minus
            | Minus =>
                match l with
                    | F => Grade F m 
                    | _ => Grade (lower_letter l) Plus
                end
        end
    end.

Example lower_grade_A_Plus : lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.
Example lower_grade_A_Natural : lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.
Example lower_grade_A_Minus : lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.
Example lower_grade_B_Plus : lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.
Example lower_grade_F_Natural : lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.
Example lower_grade_twice : lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.
Example lower_grade_thrice : lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. reflexivity. Qed.

(* =========== exercise: 3 stars, standard (lower_grade_lowers) *)
Theorem lower_grade_lowers1 :
    forall (g : grade),
        grade_comparison (Grade F Minus) g = Lt ->
        grade_comparison (lower_grade g) g = Lt.
Proof.
    intros [[] []] H;
    reflexivity || discriminate H.
Qed.

Theorem lower_grade_lowers2 :
    forall (g : grade),
        grade_comparison (Grade F Minus) g = Lt ->
        grade_comparison (lower_grade g) g = Lt.
Proof.
    intros [[] []] H;
    rewrite <- H;
    reflexivity.
Qed.

Theorem lower_grade_lowers3 :
    forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
    intros [l m] H.
    rewrite <- H.
    destruct l as []; destruct m as []; reflexivity.
Qed.

Theorem lower_grade_lowers4 :
    forall (g : grade),
        grade_comparison (Grade F Minus) g = Lt ->
        grade_comparison (lower_grade g) g = Lt.
Proof.
  intros [l m] H.
  destruct m.
  - simpl. rewrite letter_comparison_Eq. reflexivity.
  - simpl. rewrite letter_comparison_Eq. reflexivity.
  - destruct l; rewrite <- H; reflexivity.
Qed.

Theorem lower_grade_lowers5 :
    forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  intros [l m] H.
  destruct m.
  - simpl. rewrite letter_comparison_Eq. reflexivity.
  - simpl. rewrite letter_comparison_Eq. reflexivity.
  - destruct l.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- rewrite <- H, lower_grade_F_Minus. reflexivity.
Qed.

(* penalty *)
Fixpoint less_than (a b :nat) : bool :=
    match a,b with
        | _, O => false
        | O, _ => true
        | S a', S b' => less_than a' b'
    end.
Notation "x < y" := (less_than x y) (at level 70).

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
    if (late_days < 9) then g
    else if late_days < 17 then lower_grade g
    else if late_days < 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).

(* helps to prove using rewrite *)
Theorem apply_late_policy_unfold :
    forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g) = (
        if late_days < 9 then g 
        else if late_days < 17 then lower_grade g
        else if late_days < 21 then lower_grade (lower_grade g)
        else lower_grade (lower_grade (lower_grade g))
    ).
Proof.
    reflexivity.
Qed.

(* =========== exercise: 2 stars, standard (no_penalty_for_mostly_on_time) *)
Theorem no_penalty_for_mostly_on_time :
    forall (late_days : nat) (g : grade),
        (late_days < 9 = true) ->
        apply_late_policy late_days g = g.
Proof.
    intros l g H.
    rewrite apply_late_policy_unfold, H.
    reflexivity.
Qed.

(* =========== exercise: 2 stars, standard (graded_lowered_once) *)
Theorem grade_lowered_once :
    forall (late_days : nat) (g : grade),
        (late_days < 9 = false) ->
        (late_days < 17 = true) ->
        (apply_late_policy late_days g) = (lower_grade g).
Proof.
    intros a g H1 H2.
    rewrite apply_late_policy_unfold, H1, H2.
    reflexivity.
Qed.

End LateDays.


(* =========== exercise: 3 stars, standard (binary) *)
Inductive bin : Type :=
    | Z
    | B0 (n : bin)
    | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
    match m with
        | Z => B1 Z
        | B0 m' => B1 m'
        | B1 m' => B0 (incr m')
    end.

Fixpoint bin_to_nat (m:bin) : nat :=
    match m with
        | Z => O
        | B0 m' => (bin_to_nat m') + (bin_to_nat m')
        | B1 m' => S(bin_to_nat m') + (bin_to_nat m')
    end. 

Definition m : bin := (B1 (B1 (B0 (B1 (B0 (B1 Z)))))).
Compute bin_to_nat m.
Compute bin_to_nat (incr m).
Compute bin_to_nat (incr (incr m)).
Compute bin_to_nat (incr (incr (incr m))).
Compute bin_to_nat (incr (incr (incr (incr m)))).
Compute bin_to_nat (incr (incr (incr (incr (incr m))))).

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.
