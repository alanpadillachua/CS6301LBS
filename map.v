(**********************************************************************)
(*  v      *   Burrows-Wheeler transform defined in Coq.              *)
(* <O___,, *   Coquistadores  -  Copyright (c) 2017                   *)
(*   \VV/  ************************************************************)
(*    //   *   Authors:   Alan Padilla Chua, Hanlin He                *)
(*         *              Paul Parrot, Sourav Dasgupta                *)
(**********************************************************************)

(** * A possible new start to simply type. *)


(** Defined a new inductive datatype id to serve as the "index" of
    an element in a list. *)
Inductive index : Type :=
  | Index : nat -> index.

(** Equality test for index. *)
Definition beq_index x y :=
  match x,y with
    | Index n1, Index n2 => if Nat.eqb n1 n2 then true else false
  end.


(** Define a type of _total map_ that return a default value when
    we look up an index not in the list. *)
Definition total_map (A : Type) := index -> A.

Definition t_empty {A : Type} (v : A) : total_map A := (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : index) (v : A) :=
  fun x' => if beq_index x x' then v else m x'.


(** _string map_ is a partial map from index to letter. *)
Definition string_map (A : Type) := total_map (option A).

Definition empty_string {A : Type} : string_map A := t_empty None.

Definition string_update {A : Type} (m : string_map A) (x : index) (v : A) :=
  t_update m x (Some v).


(** _string matrix_ is a partial map from index to _string map_. *)
Definition string_matrix (A : Type) := total_map (option (string_map A)).

Definition empty_matrix {A : Type} : string_matrix A := @t_empty (option (string_map A)) None.

Definition matrix_update {A : Type} (m : string_matrix A) (x : index) (v : string_map A) :=
  t_update m x (Some v).


(** Standard Permutation is a map from index to index *)
Definition pi := total_map index.

Definition empty_pi := t_empty index (Index O).

Definition pi_update (p : pi) (x : index) (v : index) :=
  t_update p x v.