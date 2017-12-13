(**********************************************************************)
(*  v      *   Burrows-Wheeler transform defined in Coq.              *)
(* <O___,, *   Coquistadores  -  Copyright (c) 2017                   *)
(*   \VV/  ************************************************************)
(*    //   *   Authors:   Alan Padilla Chua, Hanlin He                *)
(*         *              Paul Parrot, Sourav Dasgupta                *)
(**********************************************************************)

Require Import List.
Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Datatypes.
Require Import List Setoid Permutation Sorted Orders Mergesort.

Local Coercion is_true : bool >-> Sortclass.

(** Notations and conventions *)

Local Notation "[ ]" := nil.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

Definition cmp (A:Type) := A -> A -> bool.

Definition eqdec (A : Set) := forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}.

(*
Local Open Scope char_scope.
Local Open Scope string_scope.
Open Scope bool_scope.
*)

Local Open Scope string_scope.

Definition HelloWorld := "Hello World!".
Definition Cat := "Cat.".

Fixpoint string_to_list (s : string): list nat := 
  match s with
  | EmptyString => nil
  | String h t => nat_of_ascii h :: string_to_list t
  end.

Fixpoint list_to_string (l : list nat) : string := 
  match l with
  | nil => EmptyString
  | h :: t => String (ascii_of_nat h) (list_to_string t)
  end.

Definition app_item {A : Type} : list A -> A -> list A :=
  fix app_item l last :=
  match l with
  | nil => last :: nil
  | h :: t => h :: app_item t last
  end.

Theorem app_item_length :
  forall (A: Type) (l : list A) (x : A), List.length (app_item l x) = S (List.length l).
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - specialize (IHl x). rewrite IHl. reflexivity.
Qed.

Infix "+++" := app_item (right associativity, at level 60) : list_scope.

Definition left_shift {A : Type} : list A -> list A :=
  fix left_shift l :=
  match l with
  | nil => nil
  | h :: t => t +++ h
  end.

Theorem left_shift_constant_length :
  forall (A: Type) (x : list A), List.length x = List.length (left_shift x).
Proof.
  induction x; simpl.
  - reflexivity.
  - rewrite app_item_length. reflexivity.
Qed.

Definition conjugacy {A : Type} : list A -> list (list A) :=
  fix conjugacy l :=
    let fix conjugacy' (l : list A) (len : nat) :=
      match len with
      | O => nil
      | S len' => l :: conjugacy' (left_shift l) len'
      end in
    conjugacy' l (List.length l).

Fixpoint last {A : Type} (l : list A) (d : A) : A :=
match l with
  | [ ] => d
  | [a] => a
  | h :: t => last t d
end.

Fixpoint last_col {A : Type} (l : list (list A)) (d : A) : list A :=
  match l with
  | [ ] => [ ]
  | h :: t => last h d :: last_col t d
  end.

(** Module to define nat total order. **)
Module NatOrder <: TotalLeBool.
  Definition t := nat.

  Theorem eqb_refl :
    forall a b : nat, Nat.eqb a b = Nat.eqb b a.
  Proof.
    induction a; destruct b; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - specialize (IHa b). exact IHa.
  Qed.

  Fixpoint leb x y :=
    match x, y with
    | 0, _ => true
    | _, 0 => false
    | S x', S y' => leb x' y'
    end.

  Local Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof.
    induction a1; destruct a2; simpl; auto.
  Qed.
End NatOrder.

(** Module to define option nat total order. **)
Module OptionNatOrder <: TotalLeBool.
  Definition t := option nat.

  Definition eqb (a1 a2 : option nat) :=
    match a1, a2 with
    | None, None => true
    | None, _ => false
    | _, None => false
    | Some a1', Some a2' => Nat.eqb a1' a2'
    end.

  Definition leb (a1 a2 : option nat) :=
    match a1, a2 with
    | None, None => true
    | None, _ => true
    | _, None => false
    | Some a1', Some a2' => NatOrder.leb a1' a2'
    end.

  Theorem eqb_refl :
    forall a b : option nat, eqb a b = eqb b a.
  Proof.
    intros. destruct a; destruct b; simpl.
    - rewrite NatOrder.eqb_refl. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof.
    destruct a1; destruct a2; simpl; auto.
    apply NatOrder.leb_total.
  Qed.
End OptionNatOrder.

(** Module to define list of option nat total order, i.e., comparator of list. **)
Module NatListOrder <: TotalLeBool.
  Definition t := list nat.

  Fixpoint eqb (l1 l2 : list nat) :=
    match l1, l2 with
    | nil, nil => true
    | nil, _ => false
    | _, nil => false
    | h1 :: t1, h2 :: t2 => if Nat.eqb h1 h2
                            then eqb t1 t2
                            else false
    end.

  Fixpoint leb (x y : list nat) := 
    match x, y with
    | nil, _ => true
    | _, nil => false
    | hx :: tx, hy :: ty => if Nat.eqb hx hy
                            then leb tx ty
                            else NatOrder.leb hx hy
    end.

  Local Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2 : list nat, a1 <=? a2 \/ a2 <=? a1.
  Proof.
    induction a1; destruct a2; simpl; auto.
    rewrite NatOrder.eqb_refl.
    destruct (Nat.eqb n a).
    - specialize (IHa1 a2). exact IHa1.
    - apply NatOrder.leb_total.
  Qed.
End NatListOrder.

Module NatZipOrder <: TotalLeBool.
  Definition t := @prod nat nat.

  Definition eqb (x y : t) :=
    match x, y with
    | pair x1 x2, pair y1 y2 => Nat.eqb x1 y1 && Nat.eqb x2 y2
    end.

  Definition leb (x y : t) :=
    match x, y with
    | pair x1 x2, pair y1 y2 => if Nat.eqb x1 y1
                                then NatOrder.leb x2 y2
                                else Nat.leb x1 y1
    end.

  Theorem eqb_refl :
    forall a b : t, eqb a b = eqb b a.
  Proof.
    intros. destruct a; destruct b; simpl.
    rewrite NatOrder.eqb_refl.
    rewrite andb_comm.
    rewrite NatOrder.eqb_refl.
    rewrite andb_comm.
    reflexivity.
  Qed.

  Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof.
    destruct a1; destruct a2; simpl; auto.
    rewrite NatOrder.eqb_refl. destruct (Nat.eqb n1 n).
    apply NatOrder.leb_total.
    apply NatOrder.leb_total.
  Qed.
End NatZipOrder.

Module Import NatSort := Sort NatOrder.
Module Import NatListSort := Sort NatListOrder.
Module Import NatZipSort := Sort NatZipOrder.

Definition bwt (s : string) : string :=
  list_to_string (last_col (NatListSort.sort (conjugacy (string_to_list s))) 1).

Eval compute in bwt "banana".

(*Example sort_bwt := Eval compute in sort bwt.*)

(*Inductive prod {A B : Type} : Type :=
| pair : A -> B -> (@prod A B).

Definition fst {A B : Type} (p : @prod A B) : A :=
  match p with
  | pair x y => x
  end.
Definition snd {A B : Type} (p : @prod A B) : B :=
  match p with
  | pair x y => y
  end.
*)

Fixpoint zip' {A : Set} (l : list A) (i : nat) : list (prod A nat) :=
  match l with
  | nil => nil
  | h :: t => (pair h i) :: zip' t (S i)
  end.

Definition zip := fun {A : Set} (l : list A) => zip' l O.


(** Get the index of an element in a list. **)

Fixpoint indexOf {A : Type} (eq : cmp A) (l : list A) (target : A) : nat :=
  let fix indexOf' {A : Type} (eq : cmp A) (l : list A) (target : A) (i : nat) : nat :=
    match l with
    | nil => length l
    | h :: t => if eq h target then i else indexOf' eq t target (S i)
    end in
  indexOf' eq l target O.

Definition update {A B : Type} (eq : cmp A) (f : A -> B) (x: A) (y: B) : A -> B := 
  fun (n : A) => if eq n x then y else f n.

Definition standard_permutation :=
  let fix standard_permutation' (start_index : nat)
                                (f : nat -> nat)
                                (A : Type)
                                (eq : cmp (@prod A nat))
                                (zipped_bwt sorted_bwt : list (@prod A nat)) :
                                nat -> nat :=
    match sorted_bwt with
    | nil => f
    | h :: t => standard_permutation' (S start_index) 
                                      (update Nat.eqb f start_index (indexOf eq zipped_bwt h))
                                      A eq zipped_bwt t
    end in
  standard_permutation' O (fun (_: nat) => 0).


Definition list_to_map :=
  fix list_to_map (eq : nat -> nat -> bool) (l : list nat) (start_index : nat) : nat -> nat :=
  let f := fun _ => length l in
  match l with
  | nil => f
  | h :: t => update eq (list_to_map eq t (S start_index)) start_index h
  end.

Definition product:=
  fix product (k : nat) (bwt_sp : nat -> nat) (i : nat) : list nat :=
    match k with
    | O => nil
    | S O => bwt_sp i :: nil
    | S k' => let product_k' := product k' bwt_sp i in
              product_k' +++ (bwt_sp (last product_k' O))
    end.


Definition ascii_of_nat_option (n : option nat) : option ascii :=
  match n with
  | None => None
  | Some n' => Some (ascii_of_nat n')
  end.

Definition inverse_bwt (s : string) (index : nat) :=
  let map_bwt := list_to_map Nat.eqb (string_to_list s) O in
  let zipped_bwt := zip (string_to_list s) in
  let sorted_bwt := sort zipped_bwt in
  (list_to_string (map map_bwt (product (String.length s) (standard_permutation (nat) NatZipOrder.eqb zipped_bwt sorted_bwt) index))).


Eval compute in inverse_bwt (bwt "Hello World!") 2.
Eval compute in inverse_bwt (bwt "banana") 3.

