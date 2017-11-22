(* Burrows-Wheeler transform defined in Coq. *)

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


Definition update f (x: nat ) (y: option nat) : nat -> option nat  := 
fun (n:nat) => 
  if Nat.eqb n x then y else f n. 
  
Definition f' := update f 0 (Some 2).

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

(*
I think it might not be easy to generate and update the matrix directly.
"matrix : nat -> nat -> option nat" can be considered as
"matrix : nat -> (nat -> option nat)", where "f : nat -> option nat" is the
mapping from index to character in one permutation of a string.
So we can first define a function to generate "f".
*)

(* Transform a string to a list of ascii. *)
Fixpoint string_to_list (s : string): list ascii := 
  match s with
    | EmptyString => nil
    | String h t => h :: string_to_list t
  end.

(* Map ascii to nat in a list. *)
Fixpoint ascii_to_nat_list (l : list ascii) : list (option nat) :=
  match l with
  | nil => nil
  | h :: t => Some (nat_of_ascii h) :: ascii_to_nat_list t
  end.

(* Transform a nat list to a index to nat mapping, i.e. nat -> option nat. *)
Fixpoint list_to_map (l : list (option nat)) (m : nat) : nat -> option nat :=
  let f := fun _ => None in
  match l with
  | nil => f
  | h :: t => update (list_to_map t (S m)) m h
  end.

(* Use function defined above, generate a index to nat mapping from given string. *)
Definition string_to_map (word : string) : nat -> option nat :=
  list_to_map (ascii_to_nat_list (string_to_list word)) O.

(* A helper function ("option nat -> option ascii") using library function
"ascii_of_nat : nat -> ascii". *)
Definition ascii_of_nat_option (a : option nat) : option ascii :=
  match a with
  | None => None
  | Some a' => Some (ascii_of_nat a')
  end.

(* Test "string_to_map". *)
Definition hello_world := string_to_map "Cat".

Definition hello_world_len := length "Cat".

Compute hello_world_len.

Compute ascii_of_nat_option (hello_world 0).
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

Definition minus_one x :=
  match x with
  | O => O
  | S x' => x'
  end.
  
  
(* Following implementation relies on length of the string,
which is hard to compute directly from the mapping,
so the previously computed value used here (not good). *)

(* Right-shift a mapping by one and return a new mapping. *)
Definition right_shift (m : nat -> option nat) : nat -> option nat :=
  fun n =>
    match n with
    | O => m hello_world_len
    | S n' => m n'
    end.

Example hello_world_r1 := right_shift hello_world.
Example hello_world_r2 := right_shift hello_world_r1.
Example hello_world_r3 := right_shift hello_world_r2.
Example hello_world_r4 := right_shift hello_world_r3.
Example hello_world_r5 := right_shift hello_world_r4.

Compute ascii_of_nat_option (hello_world_r1 0).
Compute ascii_of_nat_option (hello_world_r2 1).
Compute ascii_of_nat_option (hello_world_r3 1).
Compute ascii_of_nat_option (hello_world_r4 1).
Compute ascii_of_nat_option (hello_world_r5 1).

(* Get the first letter. *)
Definition first (m : nat -> option nat) : option nat := m O.

(* Get the last letter. *)
Definition last (m : nat -> option nat) : option nat := m hello_world_len.


(* A modified version update to update mapping of mapping. *)
Definition update'' f (x : nat) (y : nat -> option nat) : nat -> nat -> option nat := 
  fun (n:nat) => 
    if Nat.eqb n x then y else f n.


Compute minus_one hello_world_len.

Fixpoint map_to_conjugacy (m : nat -> option nat) (l: nat) : nat -> nat -> option nat :=
  let f := fun _ _ => None in
  match l with
  | O => update'' f O m
  | S l' => update'' (map_to_conjugacy m l') l (right_shift ( (map_to_conjugacy m l')  l'))
  end.


Example hello_world_matrix := map_to_conjugacy hello_world  (hello_world_len).

Compute ascii_of_nat_option (hello_world_matrix 0 0).
Compute ascii_of_nat_option (hello_world_matrix 1 0).
Compute ascii_of_nat_option (hello_world_matrix 2 0).
Compute ascii_of_nat_option (hello_world_matrix 3 0).
Compute ascii_of_nat_option (hello_world_matrix 3 2).
Compute ascii_of_nat_option (hello_world_matrix 3 3).

Fixpoint lasts (matrix : nat -> nat -> option nat) (r: nat) (c: nat) : nat -> option nat :=
  let f := fun _ => None in
  match r with
  | O => update f O (matrix O c)
  | S r' => update (lasts matrix r' c) (r) (matrix r c)
  end.


Example last_col := lasts hello_world_matrix (hello_world_len) (hello_world_len).

Compute ascii_of_nat_option (last_col 0).
Compute ascii_of_nat_option (last_col 2).
Compute ascii_of_nat_option (last_col 3).
Compute ascii_of_nat_option (last_col 11).

(* None has lowest rank. *)

Definition cmp (A:Type) := A -> A -> Prop.

Definition eqdec (A:Type) := forall x y:A, {x=y}+{x<>y}.

Definition sorter {A:Type} (leq: cmp A) (sort: (nat -> A) -> (nat -> A)) (len: nat) : Prop :=
  forall f n, S n < len -> leq (sort f n) (sort f (S n)).

Fixpoint count {A:Type} (eq:eqdec A) (x:A) (f: nat -> A) (len: nat) :=
  match len with
  | O => O
  | S m => if eq (f m) x then S (count eq x f m) else count eq x f m
  end.

Definition permuter {A:Type} (eq: eqdec A) (sort: (nat -> A) -> (nat -> A)) (len: nat) :=
  forall f x, count eq x (sort f) len = count eq x f len.











