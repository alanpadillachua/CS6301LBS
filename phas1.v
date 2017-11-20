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


