(**********************************************************************)
(*  v      *   Burrows-Wheeler transform defined in Coq.              *)
(* <O___,, *   Coquistadores  -  Copyright (c) 2017                   *)
(*   \VV/  ************************************************************)
(*    //   *   Authors:   Alan Padilla Chua, Hanlin He                *)
(*         *              Paul Parrot, Sourav Dasgupta                *)
(**********************************************************************)

Require Import List Nat Arith.
Require Import Ascii String.
Require Import Datatypes.
Require Import FunctionalExtensionality.

(*Local Open Scope char_scope.*)
Local Open Scope string_scope.
Open Scope bool_scope.

(** Define type for [char], [str], [str_matrix]. *)
Definition char := option nat.
Definition str := nat -> char.
Definition str_matrix := nat -> str.

Definition eqdec (A:Type) := forall x y:A, {x=y}+{x<>y}.

(** A generic "update" function for mapping "nat -> A". *)
(* Note: The definition might be generalized again to update mapping "A -> B",
 * but it would require to implement or pass as input an alternative comparing
 * function other than "Nat.eqb". *)


Definition update {A : Type} (f : nat -> A) (x: nat) (y: A) : nat -> A := 
  fun (n : nat) => if Nat.eq_dec n x then y else f n.

(** Transform a string to a list of ascii. *)
Fixpoint string_to_list (s : string): list ascii := 
  match s with
  | EmptyString => nil
  | String h t => h :: string_to_list t
  end.

(** Map ascii to nat in a list. *)
Fixpoint ascii_to_nat_list (l : list ascii) : list char :=
  match l with
  | nil => nil
  | h :: t => Some (nat_of_ascii h) :: ascii_to_nat_list t
  end.

(** Transform a nat list to a index -> nat mapping, i.e. nat -> option nat. *)
Fixpoint list_to_map (l : list char) (start_index : nat) : str :=
  match l with
  | nil => fun _ => None
  | h :: t => update (list_to_map t (S start_index)) start_index h
  end.

(** Use function defined above, generate a index to nat mapping from given string. *)
Definition string_to_map (word : string) : str :=
  list_to_map (ascii_to_nat_list (string_to_list word)) O.

(** helper functions **)
(* "option_ascii_of_nat_option : option nat -> option ascii" using library function "ascii_of_nat : nat -> ascii". *)
Definition option_ascii_of_nat_option (n : char) : option ascii :=
  match n with
  | None => None
  | Some n' => Some (ascii_of_nat n')
  end.
(* "option_nat_of_ascii_option : option ascii -> option nat" using library function "nat_of_ascii : ascii -> nat". *)
Definition option_nat_of_ascii_option (a : option ascii) : char :=
  match a with
  | None => None
  | Some a' => Some (nat_of_ascii a')
  end.

(*  Alternative definition of "string_to_map", which use library function
    "get : nat -> string -> option ascii" directly. *)
Definition string_to_map' (word : string) : str :=
  fun n => option_nat_of_ascii_option (get n word).

(*  Mirror theorem for "ascii_nat_embedding" with option. *)
Theorem ascii_nat_embedding_option :
  forall a : option ascii, option_ascii_of_nat_option (option_nat_of_ascii_option a) = a.
Proof.
  intros.
  destruct a.
  - simpl. rewrite -> ascii_nat_embedding. reflexivity.
  - simpl. reflexivity.
Qed.

(** Test "string_to_map". **)
Definition hello_world_str := "Hello World!".
Definition cat_str := "Cat".

Definition hello_world := string_to_map hello_world_str.
Definition hello_world_length := String.length hello_world_str.

Definition cat := string_to_map cat_str.
Definition cat_length := String.length cat_str.

(** Prove that if given "list_to_map" a different index, to get the same element,
    the parameter to the mapping should change the same difference. *)
Lemma list_to_map_index_difference:
  forall (l : list char) (m n : nat),
    (list_to_map l m) n = (list_to_map l (S m)) (S n).
Proof.
  induction l; intros; simpl.
  - reflexivity.
  - unfold update. simpl. destruct (Nat.eq_dec n m).
    + reflexivity.
    + specialize (IHl (S m) n). exact IHl.
Qed.

(** Prove that if prepend a character to a string, to get the same character again,
    increase the index by 1. *)
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
    option_ascii_of_nat_option (string_to_map s n) = String.get n s.
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
    option_ascii_of_nat_option (string_to_map' s n) = String.get n s.
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
Definition right_shift (m : str) (l : nat) : str :=
  fun n =>
    match n with
    | O => m l
    | S n' => m n'
    end.

Example hello_world_r1 := right_shift hello_world hello_world_length.
Example hello_world_r2 := right_shift hello_world_r1 hello_world_length.
Example hello_world_r3 := right_shift hello_world_r2 hello_world_length.
Example hello_world_r4 := right_shift hello_world_r3 hello_world_length.
Example hello_world_r5 := right_shift hello_world_r4 hello_world_length.

Compute option_ascii_of_nat_option (hello_world_r1 0).
Compute option_ascii_of_nat_option (hello_world_r2 1).
Compute option_ascii_of_nat_option (hello_world_r3 1).
Compute option_ascii_of_nat_option (hello_world_r4 1).
Compute option_ascii_of_nat_option (hello_world_r5 1).


(** String start with index 0. *)

(** Get the first letter. *)
Definition first (m : str) : char := m O.

(** Get the last letter. *)
Definition last (m : str) (length : nat) : char :=
  match length with
  | O => None
  | S length' => m length'
  end.

Eval compute in last hello_world hello_world_length.

(* functional extensionality *)

(** Generate right-shift permutation matrix of the string mapping. **)
(*  Helper recursion definition, which keeps a constant length through recursion. *)
Fixpoint map_to_conjugacy' (m : str) (l length: nat) := (* Define the actual recursive function, induction on l. *)
    match l with
    | O => update (fun _ _ => None) O m
    | S l' => let l'_conjugacy := map_to_conjugacy' m l' length in
              update l'_conjugacy l (right_shift (l'_conjugacy l') length)
    end.

Definition map_to_conjugacy (m : str) (length: nat) : str_matrix :=
  map_to_conjugacy' m length length.

Example hello_world_matrix := map_to_conjugacy hello_world hello_world_length.

Compute option_ascii_of_nat_option (hello_world_matrix 0 0).
Compute option_ascii_of_nat_option (hello_world_matrix 1 0).
Compute option_ascii_of_nat_option (hello_world_matrix 2 0).
Compute option_ascii_of_nat_option (hello_world_matrix 3 0).
Compute option_ascii_of_nat_option (hello_world_matrix 3 2).
Compute option_ascii_of_nat_option (hello_world_matrix 3 3).

(** Extract the last column from the matrix. **)
(* Originally both "r" and "c" were passed as parameter, and induction on r.
 * Now only length is passed, and internally a constant "last_col_index" was kept,
 * and induction directly on length. *)

Fixpoint lasts' (matrix : str_matrix) (row length : nat) :=
  match row with
  | O => update (fun _ => None) O (matrix O length)
  | S row' => update (lasts' matrix row' length) row (matrix row length)
  end.

Definition lasts (matrix : str_matrix) (length : nat) : str :=
  lasts' matrix length length.

Example last_col := lasts hello_world_matrix hello_world_length.

Compute option_ascii_of_nat_option (last_col 0).
Compute option_ascii_of_nat_option (last_col 1).
Compute option_ascii_of_nat_option (last_col 2).
Compute option_ascii_of_nat_option (last_col 3).
Compute option_ascii_of_nat_option (last_col 11).

Fixpoint map_to_string' (len : nat) (i : nat) (map : str) : string :=
  match len with
  | O => EmptyString
  | S len' => match option_ascii_of_nat_option (map i) with
              | Some a => String a (map_to_string' len' (S i) map)
              | None => map_to_string' len' (S i) map
              end
  end.

Definition map_to_string (len : nat) (map : str) : string :=
  map_to_string' len (S O) map.

Eval compute in map_to_string hello_world_length last_col.

(** Define whether two [str]s are reverse of each other at lenght "n". *)
Definition reverse_str (n : nat) (f1 f2 : str) : Prop :=
  forall (n1 n2: nat), n1 + n2 = n <-> f1 n1 = f2 n2.

(** Define whether two [str]s are the same. *)
Definition same_str (f1 f2 : str) : Prop :=
  forall (n : nat), f1 n = f2 n.

(** Prove that the last column of the right-shift permutation matrix is the reverse of the original string mapping. **)
Theorem last_col_reverse:
  forall (s : string) (l : nat) (m : nat -> option nat),
    l = String.length s -> m = string_to_map s -> reverse_str l m (lasts (map_to_conjugacy m l) l).
Proof.
  intros.
  unfold map_to_conjugacy.
  unfold lasts.
Abort.

Definition bwt (s : string) (sort: (nat -> nat -> option nat) -> (nat ->  nat -> option nat)) : string :=
  let s_length := String.length s in
  let s_map := string_to_map s in
  let s_matrix := map_to_conjugacy s_map s_length in
  let sorted_matrix := sort s_matrix in
  map_to_string s_length (lasts sorted_matrix s_length).

(* An example bwt without sorting. *)
Eval compute in bwt hello_world_str (fun x => x).


(** Option nat order. *)
Definition optnat_leq (x y : option nat) :=
  match y with None => True | Some n =>
    match x with None => False | Some m => m <= n end
  end.

(** Option nat equility. *)
Definition optnat_eqb (a1 a2 : option nat) :=
  match a1, a2 with
  | None, None => True
  | None, _ => False
  | _, None => False
  | Some a1', Some a2' => Nat.eqb a1' a2' = true
  end.

(** Generic sequence leq ordering. *)
Fixpoint leq_seq {A:Type} (eq leq : A -> A -> Prop) (k : nat) (s1 s2 : nat -> A) : Prop :=
  match k with
  | O => leq (s1 O) (s2 O)
  | S m => (eq (s1 O) (s2 O) /\ leq_seq eq leq m (fun i => s1 (S i)) (fun i => s2 (S i)))
            \/ leq (s1 O) (s2 O)
  end.

(** Generic sequence equility based on leq. *)
Fixpoint eq_seq {A:Type} (eq : A -> A -> Prop) (k : nat) (s1 s2 : nat -> A) : Prop :=
  match k with
  | O => eq (s1 O) (s2 O)
  | S m => eq (s1 O) (s2 O) /\ eq_seq eq m (fun i => s1 (S i)) (fun i => s2 (S i))
  end.

(** Option nat sequence leq ordering based on leq_seq. *)
Definition leq_optnatctx (k : nat) (s1 s2 : str) : Prop :=
  leq_seq optnat_eqb optnat_leq k s1 s2.

(** Option nat sequence equility  based on eq_seq. *)
Definition eq_optnatctx (k : nat) (s1 s2 : str) : Prop :=
  eq_seq optnat_eqb k s1 s2.

(** String matrix sequence equility  based on eq_seq. *)
Definition eq_matrix (k : nat) (s1 s2 : str_matrix) : Prop :=
  eq_seq (eq_optnatctx k) k s1 s2.

(** String leq ordering for all context. *)
Definition leq_optnatseq s1 s2 := forall k, leq_optnatctx k s1 s2.

(** The image of function f is sorted with respect to order relation R. *)
Definition sorted {A:Type} (R: A -> A -> Prop) (f: nat -> A) :=
  forall i, R (f i) (f (S i)).

(* If relation R is reflexive and transitive, then image(f)'s ordering is also transitive. *)
Definition reflexive {A:Type} (R: A -> A -> Prop) :=
  forall a, R a a.

Definition transitive {A:Type} (R: A -> A -> Prop) :=
  forall a c b, R a b -> R b c -> R a c.

Theorem sorted_transitive {A:Type}
  (R: A -> A -> Prop) (RE: reflexive R) (TR: transitive R) :
  forall (f: nat -> A) (SRT: sorted R f) i j, i <= j -> R (f i) (f j).
Proof.
  intros f SRT i j. revert i. induction j; intros; inversion H.
    apply RE.
    apply RE.
    eapply TR. apply IHj. assumption. apply SRT.
Qed.

(* Permutation functions are injective and surjective. *)
Definition injective {A B:Type} (f: A -> B) :=
  forall i j, f i = f j -> i=j.

Definition surjective {A B:Type} (f: A -> B) :=
  forall j, exists i, f i = j.

Definition bijective {A B:Type} (f: A -> B) :=
  injective f /\ surjective f.



(* Return the character at position i of string m *)
Definition lambda (m:nat -> option nat) (i:nat) := m i.

(* Returns the position of an alphabet 'char' in string 'm' of length 'length' *)
Fixpoint get_pos (eq:eqdec (option nat)) (m:nat -> option nat) (length:nat) (char: option nat) : nat :=
  match length with
  |0 => if (eq (m 0) char) then 0 else (S length)
  |S l => if (eq (m length) char) then length else (get_pos eq m l char)
  end. 

(* Introduce sorted string as assumption, not sort it inside. *)
Definition pi (eq:eqdec (option nat)) (length:nat) (m sorted_m: str) : (nat -> nat):=
fun (x:nat) => get_pos eq (sorted_m) length (m x).

Definition context (k:nat) (m: nat -> (option nat)) : (nat -> (option nat)) :=
fun (x:nat) => if (x <? k) then (m x) else None.

(* Use [pi'] instead of [pi]. *)
Fixpoint inverse_bwt' (eq:eqdec (option nat)) (tot_length:nat) (i k:nat) (m sorted_m :nat -> (option nat)) : (nat-> nat) :=
let p' := (pi eq k m sorted_m) in
let f := fun _ => (S tot_length) in
match k with
|O => f
|S l => let rec :=  (inverse_bwt' eq tot_length i l m sorted_m) in 
       update rec k (p'(rec l)) (*  (lambda m ((pi eq l sort rec) k))   *)
end.

(** Use [inverse_bwt']. *)
Definition inverse_bwt (eq:eqdec (option nat)) (tot_length:nat) (i k:nat) (m sorted_m: str) :=
fun n => lambda m (inverse_bwt' eq tot_length i k m sorted_m n).

(* We tried to define what is a sorted string and string matrix. *)
Definition sorted_str (m m_sorted: str) (k : nat) : Prop := True.
Definition sorted_matrix (matrix : str_matrix) (k : nat) : Prop := True.

(* Length is then a property like the following: *)
Definition haslen {A:Type} (f : nat -> option A) (len: nat) :=
  (*forall i, len <= i <-> f i = None.*)
  forall l, l > len -> f l = None.

Definition prepend (s : str) (c : option nat) : str :=
  fun n =>
    match n with
    | O => c
    | S n' => s n'
    end.

Definition concat (s1 s2: str) (l1 l2 : nat) : str :=
  fun n => if leb n l1 then s1 n else s2 (n - l1).

(** *)
Lemma context_k (w: str_matrix) (L : str) (length : nat) :
  forall (k i : nat),
    k <= length ->
    i <= length ->
    same_str (context (S k) (right_shift (w i) length)) (prepend (context k (w i)) (lambda L i)).
Proof.
  induction k.
  - intros. unfold right_shift.
Admitted.

Definition right_shift_matrix (w: str_matrix) (length : nat) : str_matrix :=
  fun n => right_shift (w n) length.

Lemma Right_Shift (w : str_matrix) (length : nat) (sort : nat -> str_matrix -> str_matrix) :
  forall t , 
    t < length ->
    sorted (leq_optnatctx t) w ->
    eq_matrix (S t) (sort 1 (right_shift_matrix w length)) (sort (S t) (right_shift_matrix w length)).
Proof.
Admitted.

Lemma sort_matrix (w: str_matrix) (length : nat) (k : nat) (sort : nat -> str_matrix -> str_matrix) (pi : nat -> nat) :
  sorted_matrix w k ->
  forall (n : nat), same_str (sort (S k) (right_shift_matrix w length) n) (right_shift (w (pi n)) length).
Proof.
Admitted.

Lemma matrix' (w1 w2 : str_matrix) (L L_sorted: str) (length : nat) (eq:eqdec (option nat)) (k : nat) :
  forall (i: nat) ,
    i <= length ->
    haslen L length ->
    haslen L_sorted length ->
    sorted_matrix w1 k ->
    sorted_matrix w2 k ->
    sorted (leq_optnatctx k) w1 ->
    same_str L (lasts w1 length) ->
    sorted_str L L_sorted length ->
    forall x : nat, x <= k -> same_str (context x (w1 i)) (inverse_bwt eq length i x L L_sorted).
Proof.
  induction x.
  intros. 
  unfold same_str.
  unfold context.
  unfold inverse_bwt.
  intro n. destruct n; simpl.
  unfold lambda. rewrite H0. reflexivity. auto.
  unfold lambda. rewrite H0. reflexivity. auto.
Abort.

