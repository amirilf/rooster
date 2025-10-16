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

(* ============ *)

