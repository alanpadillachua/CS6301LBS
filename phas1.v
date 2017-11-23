(* Burrows-Wheeler transform defined in Coq.
 *
 * Copyright (c) 2017
 *
 * Author: 
 *          Alan Padilla Chua
 *          Hanlin He
 *          Paul Parrot
 *          Sourav Dasgupta
 *)

Require Import List.
Require Import Ascii.
Require Import String.

Local Open Scope char_scope.
Local Open Scope string_scope.

(** A generic "update" function for mapping "nat -> A". **)
(* Note: The definition might be generalized again to update mapping "A -> B",
 * but it would require to implement or pass as input an alternative comparing
 * function other than "Nat.eqb". *)
Definition update {A : Type} (f : nat -> A) (x: nat) (y: A) : nat -> A := 
  fun (n : nat) => if Nat.eqb n x then y else f n. 

(** Transform a string to a list of ascii. **)
Fixpoint string_to_list (s : string): list ascii := 
  match s with
  | EmptyString => nil
  | String h t => h :: string_to_list t
  end.

(** Map ascii to nat in a list. **)
Fixpoint ascii_to_nat_list (l : list ascii) : list (option nat) :=
  match l with
  | nil => nil
  | h :: t => Some (nat_of_ascii h) :: ascii_to_nat_list t
  end.

(** Transform a nat list to a index -> nat mapping, i.e. nat -> option nat. **)
Fixpoint list_to_map (l : list (option nat)) (start_index : nat) : nat -> option nat :=
  let f := fun _ => None in
  match l with
  | nil => f
  | h :: t => update (list_to_map t (S start_index)) start_index h
  end.

(** Use function defined above, generate a index to nat mapping from given string. **)
Definition string_to_map (word : string) : nat -> option nat :=
  list_to_map (ascii_to_nat_list (string_to_list word)) O.

(** helper functions **)
(* "option nat -> option ascii" using library function "ascii_of_nat : nat -> ascii". *)
Definition ascii_of_nat_option (n : option nat) : option ascii :=
  match n with
  | None => None
  | Some n' => Some (ascii_of_nat n')
  end.
(* "option ascii -> option nat" using library function "nat_of_ascii : ascii -> nat". *)
Definition nat_of_ascii_option (a : option ascii) : option nat :=
  match a with
  | None => None
  | Some a' => Some (nat_of_ascii a')
  end.

(* Mirror theorem for "ascii_nat_embedding" with option. *)
Theorem ascii_nat_embedding_option :
  forall a : option ascii, ascii_of_nat_option (nat_of_ascii_option a) = a.
Proof.
  intros.
  destruct a.
  - simpl. rewrite -> ascii_nat_embedding. reflexivity.
  - simpl. reflexivity.
Qed.

(* Alternative definition of "string_to_map", which use library function
   "get : nat -> string -> option ascii" directly. *)
Definition string_to_map' (word : string) : nat -> option nat :=
  fun n => nat_of_ascii_option (get n word).

(** Test "string_to_map". **)
Definition hello_world_str := "Hello World!".
Definition cat_str := "Cat".

Definition hello_world := string_to_map hello_world_str.
Definition hello_world_length := length hello_world_str.

Definition cat := string_to_map cat_str.
Definition cat_length := length cat_str.

(**
Prove that if given "list_to_map" a different index, to get the same element,
the parameter to the mapping should change the same difference.
**)
Lemma list_to_map_index_difference:
  forall (l : list (option nat)) (m n : nat),
    (list_to_map l m) n = (list_to_map l (S m)) (S n).
Proof.
  induction l; intros; simpl.
  - reflexivity.
  - unfold update. simpl. destruct (Nat.eqb n m).
    + reflexivity.
    + specialize (IHl (S m) n). exact IHl.
Qed.

(**
Prove that if prepend a character to a string, to get the same character again,
increase the index by 1.
**)
Lemma prepend_string_to_map: 
  forall (s : string) (n : nat) (a : ascii),
    string_to_map s n = string_to_map (String a s) (S n).
Proof.
  unfold string_to_map.
  induction s; induction n; simpl; unfold update; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite list_to_map_index_difference. reflexivity.
Qed.

(** Prove the "string_to_map" create right mapping. **)
Theorem String_to_Map:
  forall (s : string) (n : nat),
    ascii_of_nat_option (string_to_map s n) = get n s.
Proof.
  induction s; intro n.
  - simpl. reflexivity.
  - destruct n; simpl.
    + rewrite -> ascii_nat_embedding. reflexivity.
    + rewrite <- prepend_string_to_map. specialize (IHs n). exact IHs.
Qed.

(** Prove the "string_to_map'" create right mapping, might be trivial. **)
Theorem String_to_Map':
  forall (s : string) (n : nat),
    ascii_of_nat_option (string_to_map' s n) = get n s.
Proof.
  induction s; intros; simpl.
  - reflexivity.
  - induction n; unfold string_to_map'; simpl.
    + rewrite -> ascii_nat_embedding. reflexivity.
    + rewrite -> ascii_nat_embedding_option. reflexivity.
Qed.

(* Following implementation relies on length of the string,
which is hard to compute directly from the mapping,
so the previously computed value used here (not good). *)

(* Right-shift a mapping by one and return a new mapping. *)
Definition right_shift (m : nat -> option nat) : nat -> option nat :=
  fun n =>
    match n with
    | O => m hello_world_length
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
Definition last (m : nat -> option nat) : option nat := m hello_world_length.


Fixpoint map_to_conjugacy (m : nat -> option nat) (l: nat) : nat -> nat -> option nat :=
  let f := fun _ _ => None in
  match l with
  | O => update f O m
  | S l' => update (map_to_conjugacy m l') l (right_shift ( (map_to_conjugacy m l')  l'))
  end.


Example hello_world_matrix := map_to_conjugacy hello_world (hello_world_length).

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


Example last_col := lasts hello_world_matrix (hello_world_length) (hello_world_length).

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











