Inductive bool : Type :=
    | true
    | false.

(* =========== not with truth table *)

Definition not (b:bool) : bool :=
    match b with
        | true => false
        | false => true
    end.

Example test_not_1: (not true) = false.
Proof. simpl. reflexivity. Qed.

Example test_not_2: (not false) = true.
Proof. simpl. reflexivity. Qed.

(* =========== or with truth table *)

Definition or (b1:bool) (b2:bool) : bool :=
    match b1 with
        | true => true
        | false => b2
    end.

Example test_or_1: (or false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_or_2: (or false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_or_3: (or true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_or_4: (or true true) = true.
Proof. simpl. reflexivity. Qed.

(* =========== and with truth table *)

Definition and (b1:bool) (b2:bool) : bool :=
    match b1 with
        | true => b2
        | false => false
    end.

Example test_and_1: (and false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_and_2: (and false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_and_3: (and true false) = false.
Proof. simpl. reflexivity. Qed.

Example test_and_4: (and true true) = true.
Proof. simpl. reflexivity. Qed.

(* =========== custom symbols with order *)

Notation "x && y" := (and x y).
Notation "x w@d2# y" := (or x (not y)) (at level 10, left associativity).

Compute (false w@d2# false).

Example test_mine: false  w@d2# true = false.
Proof. simpl. reflexivity. Qed.

(* =========== expression way *)

Definition not' (b:bool) : bool :=
    if b then false else true.

Definition and' (b1:bool) (b2:bool) : bool :=
    if b1 then b2 else false.

Definition or' (b1:bool) (b2:bool) : bool :=
    if b1 then true else b2.

(* =========== a custom 2-state type (like booleans) *)

Inductive cl : Type :=
    | black
    | white.

Definition rev (c:cl) : cl :=
    if c then white else black.

Compute (rev white).
Compute (rev black).

(* =========== EX1 * nand
   b1 b2 and nand
   f  f   f   t  
   f  t   f   t
   t  f   f   t 
   t  t   t   f 
*)

Definition nand (b1:bool) (b2:bool) : bool :=
    not (and b1 b2).

Example test_nand_1: (nand false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand_2: (nand false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand_3: (nand true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand_4: (nand true true) = false.
Proof. simpl. reflexivity. Qed.

(* pure way *)

Definition nand' (b1:bool) (b2:bool) : bool :=
    if b1 then
        if b2 then false
        else true
    else true.

Example test_nand'_1: (nand' false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand'_2: (nand' false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand'_3: (nand' true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand'_4: (nand' true true) = false.
Proof. simpl. reflexivity. Qed.

(* =========== check admitted *)

Example test_admitted: true = false.
Admitted.

(* =========== EX2 * and with 3 params *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    if (and b1 b2) then (and b2 b3) else false.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

