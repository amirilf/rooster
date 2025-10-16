(* =========== EX10 * identity_fn_applied_twice *)
Theorem identity_fn_applied_twice :
    forall (f : bool -> bool), (forall (x : bool), f x = x) 
    -> forall (b : bool), f (f b) = b.
Proof.
    intros f H x.
    rewrite H.
    rewrite H.
    reflexivity.
Qed.


(* =========== EX11 * negation_fn_applied_twice *)
Theorem neg_of_neg : forall b : bool, negb (negb b) = b.
Proof.
    intros [].
    - reflexivity.
    - reflexivity.
Qed.

(* could also be proved directly *)
Theorem negation_fn_applied_twice :
    forall (f : bool -> bool), (forall (x : bool), f x = negb x) 
    -> forall (b : bool), f (f b) = b.
Proof.
    intros f H x.
    rewrite H.
    rewrite H.
    rewrite neg_of_neg.
    reflexivity.
Qed.


(* =========== EX12 * andb_eq_orb *)

Theorem a_is_orb_when_true : forall a b : bool, a = true -> orb a b = true.
Proof.
    intros [] [] H.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite H. reflexivity. 
Qed.

Theorem a_is_andb_when_false : forall a b : bool, a = false -> andb a b = false.
Proof.
    intros [] [] H.
    - rewrite H. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. 
Qed.

Theorem a_is_andb_with_true : forall a : bool, andb true a = a.
Proof.
    intros a.
    reflexivity.
Qed.

Theorem a_is_orb_with_false : forall a : bool, orb false a = a.
Proof.
    intros a.
    reflexivity.
Qed.

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
    destruct a as [] eqn:Ea.
        - simpl in *. rewrite <- H. reflexivity.
        - simpl in *. rewrite <- H. reflexivity.
Qed.

Theorem andb_eq_orb3 : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
    intros a b.
    destruct a.
        - simpl. intros H. rewrite -> H. reflexivity.
        - simpl. intros H. rewrite -> H. reflexivity.
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


(* =========== EX13 * letter_comparison_Eq *)
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


(* =========== EX14 ** grade_comparison *)
Definition grade_comparison (g1 g2 : grade) : comparison :=
    match g1, g2 with Grade l1 m1, Grade l2 m2 =>
        match letter_comparison l1 l2 with
            | Eq => modifier_comparison m1 m2
            | any => any
        end
    end.

Example test_grade_comparison1 : (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 : (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3 : (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4 : (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

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


Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

(* =========== EX15 ** lower_letter_lowers *)

Theorem lower_letter_lowers: 
    forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
    intros l H.
    destruct l as [] eqn:E.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - discriminate.
    (* - rewrite <- H. simpl. reflexivity. *)
    (* - simpl. apply H. *)
Qed.


(* =========== EX16 ** lower_grade *)
Definition lower_grade (g : grade) : grade :=
    match g with | Grade l m =>
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


(* =========== EX17 ** lower_grade_lowers *)
Theorem lower_grade_lowers :
    forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
Qed.



End LateDays.
