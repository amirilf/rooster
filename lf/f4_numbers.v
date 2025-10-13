Module MyModule.
    Inductive nat : Type :=
        | O
        | S (n : nat).

    Definition sub (n : nat) : nat :=
        match n with
            | O => O
            | S n' => n'
        end.

    Definition add (n : nat) : nat :=
        match n with
            | O => S O
            | S n' => S (S n')
        end.

    Definition better_add (n : nat) : nat :=
        S n.

    Compute sub (S (S (S (S O)))).
    Compute add (S (S (S (S O)))).
    Compute add (S (S O)).
    Compute better_add (S (S (S (S O)))).
    Compute better_add (S (S O)).

End MyModule.
