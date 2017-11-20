
Require Import List.
Require Import Ascii.
Require Import String.

Local Open Scope char_scope.
Local Open Scope string_scope.

Definition f : nat -> option nat := 
fun n =>
  if Nat.eqb n 0 then Some 1 else
  if Nat.eqb n 2 then Some 5 else
  if Nat.eqb n 5 then Some 13 else None.

Eval compute in f 0.
Eval compute in f 2.
Eval compute in f 5.
Eval compute in f 10.


Definition update f (x y:nat) : nat -> option nat  := 
fun (n:nat) => 
  if Nat.eqb n x then Some y else f n. 
  
Definition f' := update f 0 2.

Compute f' 0.

Compute f' 2.

Definition b : nat -> nat -> option nat := 
fun n n' => None.

Definition update' f (x y z:nat) : nat -> nat -> option nat  := 
fun (n n':nat) => 
  if (andb (Nat.eqb n x) (Nat.eqb n' y))
      then Some z else f n n'.

Compute b 0 0.

Compute (update' b 0 0 2) 0 0.



Compute (update' (update' b 0 0 2) 0 0 3) 0 0.

Definition matrix := (update' (update' (update' (update' b 0 0 3) 0 1 7) 1 0 9) 1 1 4).

Compute matrix 0 0.
Compute matrix 1 0.
Compute matrix 0 1.
Compute matrix 1 1.
Compute matrix 3 0.

Fixpoint string_to_list (s : string): list ascii := 
  match s with
    | EmptyString => nil
    | String h t => h :: string_to_list t
end.

Fixpoint ascii_to_nat_list (l : list ascii) : list nat :=
  match l with
  | nil => nil
  | h :: t => nat_of_ascii h :: ascii_to_nat_list t
end.

Fixpoint list_to_map (l : list nat) (m : nat) : nat -> option nat :=
  let f := fun x => None in
  match l with
  | nil => f
  | h :: t => update (list_to_map t (S m)) m h
  end.

Definition string_to_map (word : string) : nat -> option nat :=
  list_to_map (ascii_to_nat_list (string_to_list word)) O.

Definition hello_world := string_to_map """Hello world!""".

Definition ascii_of_nat_option (a : option nat) : option ascii :=
  match a with
  | None => None
  | Some a' => Some (ascii_of_nat a')
  end.

Compute ascii_of_nat_option (hello_world 1).
Compute ascii_of_nat_option (hello_world 2).
Compute ascii_of_nat_option (hello_world 3).
Compute ascii_of_nat_option (hello_world 4).
Compute ascii_of_nat_option (hello_world 5).
Compute ascii_of_nat_option (hello_world 6).
Compute ascii_of_nat_option (hello_world 7).
Compute ascii_of_nat_option (hello_world 8).
Compute ascii_of_nat_option (hello_world 9).
Compute ascii_of_nat_option (hello_world 10).
Compute ascii_of_nat_option (hello_world 11).
Compute ascii_of_nat_option (hello_world 12).
Compute ascii_of_nat_option (hello_world 13).
Compute ascii_of_nat_option (hello_world 14).




