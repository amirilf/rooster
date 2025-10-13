Inductive myType : Type :=
    | f
    | s.

Inductive myBool : Type :=
    | truee
    | falsee.

Definition not (b:myBool) :=
    match b with
        | truee => f
        | falsee => s
    end.

Check f.
Check truee.

Check truee : myBool.
Check truee: myBool.
Check (not truee): myType.
Check not: myBool -> myType.

(* ============== old types *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition is_red (c : color) : myBool :=
    match c with
        | primary red => truee
        | _ => falsee
    end.

Compute (is_red (white)).
Compute (is_red (primary blue)).
Compute (is_red (primary red)).

(* ============== checking modules *)

Module MyModule.
    Definition is_white (c:color) : myBool :=
        match c with
            | white => truee
            | _ => falsee
        end.
    Definition fav_color : color := primary blue.

    Module MyInner.
        Definition always_true {A : Type} (o : A) : bool := true.
    End MyInner.
End MyModule.

Check MyModule.is_white.
Check MyModule.fav_color.

Compute MyModule.is_white black.
Compute MyModule.is_white white.
Compute MyModule.fav_color.

Compute MyModule.MyInner.always_true black.
Compute MyModule.MyInner.always_true red.
Compute MyModule.MyInner.always_true falsee.

(* ============== tuples *)

Inductive bit : Type :=
    | O
    | I.

Inductive nybble : Type :=
    | bits4 (b3 b2 b1 b0 : bit).

Inductive byte : Type :=
  | nybbles (n1 n0 : nybble)
  | bits8 (b7 b6 b5 b4 b3 b2 b1 b0 : bit).

Check (bits4 O O O O).
Check (nybbles (bits4 O O I O) (bits4 O I I I)).
Check (bits8 O O I O O I I I).

(* ======== working with a byte to check if it's more than 7 *)


Definition bit_to_bool (b : bit) : bool :=
  match b with
    | O => false
    | I => true
  end.

Definition bit_or (b1 b2 : bit) : bit := 
    match b1 with
        | O => b2
        | I => b1
    end.

Notation "x || y" := (bit_or x y) (at level 50, left associativity).

Definition more_than_7 (b : byte) : bool :=
    match b with
        | bits8 b7 b6 b5 b4 b3 b2 b1 b0 =>
            bit_to_bool (b7 || b6 || b5 || b4 || b3)
        | nybbles n1 n0 =>
            match n1 with
                | bits4 b7 b6 b5 b4 =>
                    match n0 with
                        | bits4 b3 _ _ _ =>
                            bit_to_bool (b7 || b6 || b5 || b4 || b3)
                    end
            end
    end.

Compute more_than_7 (bits8 O O O O O O I I).
Compute more_than_7 (bits8 O O O I O O O O).
Compute more_than_7 (nybbles (bits4 O O O O) (bits4 O O O O)).
Compute more_than_7 (nybbles (bits4 O I O O) (bits4 O O O O)).

(* proving? *)

Lemma more_than_7_correct_bits8 :
  forall b7 b6 b5 b4 b3 b2 b1 b0 : bit,
    more_than_7 (bits8 b7 b6 b5 b4 b3 b2 b1 b0) =
    bit_to_bool (b7 || b6 || b5 || b4 || b3).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.