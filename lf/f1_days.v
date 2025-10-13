Inductive day : Type :=
  | shan
  | yesh
  | dosh
  | sesh
  | chas
  | panj
  | jome.

Definition next_working_day (d : day) : day :=
  match d with
  | shan => yesh
  | yesh => dosh
  | dosh => sesh
  | sesh => chas
  | chas => panj
  | panj => jome
  | jome => shan
  end.

Compute next_working_day chas.
Compute next_working_day (next_working_day yesh).


Example test1:
  (next_working_day (next_working_day dosh)) = chas.
Proof. simpl. reflexivity. Qed.
