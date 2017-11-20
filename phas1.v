Definition f : nat -> option nat := 
fun n =>
  if Nat.eqb n 0 then Some 1 else
  if Nat.eqb n 2 then Some 5 else
  if Nat.eqb n 5 then Some 13 else None.

Eval compute in f 0.
Eval compute in f 2.
Eval compute in f 5.
Eval compute in f 10.

Definition Update f (x y:nat) : nat -> option nat  := 
fun (n:nat) => 
  if Nat.eqb n x then Some y else f n. 
  
Definition f' := Update f 0 2.

Compute f' 0.

Compute f' 2.

