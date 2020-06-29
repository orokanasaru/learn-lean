import tactic.basic
import .ch07_indprop

open nat (succ)

open poly (prod)
open indprop (even even_four even_four' even_add_four)
open indprop.even

variables {α : Type}
variables {x y : α}
variables {P Q R : Prop}

namespace proofobjects

/-
Print even.
(* ==>
  Inductive even : nat -> Prop :=
    | ev_0 : even 0
    | ev_SS : forall n, even n -> even (S (S n)).
*)
-/

#print even

/-
Check ev_SS.
(* ===> ev_SS : forall n,
                  even n ->
                  even (S (S n)) *)
-/

#check ev_ss

/-
Theorem ev_4 : even 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.
-/

/-
Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
     : even 4  *)
-/

#print even_four

/-
Check (ev_SS 2 (ev_SS 0 ev_0)).
(* ===> even 4 *)
-/

#check ev_ss (ev_ss ev_0)

/-
Theorem ev_4': even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.
-/

#print even_four'

/-
Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.
-/

theorem even_four'' : even 4 :=
begin
  trace_state,
  apply ev_ss,
  trace_state,
  apply ev_ss,
  trace_state,
  apply ev_0,
  trace_state,
end

/-
Definition ev_4''' : even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).
-/

def even_four''' : even 4 := ev_ss (ev_ss ev_0)

/-
Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
-/

#print even_four
#print even_four'
#print even_four''
#print even_four'''

/-
Theorem ev_8 : even 8.
Proof.
  (* FILL IN HERE *) Admitted.

Definition ev_8' : even 8
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

theorem even_eight : even 8 := by { repeat { constructor, }, }

def ev_8' : even 8 := ev_ss (ev_ss even_four)

/-
Theorem ev_plus4 : ∀n, even n → even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.
-/

#print even_add_four

/-
Definition ev_plus4' : ∀n, even n → even (4 + n) :=
  fun (n : nat) ⇒ fun (H : even n) ⇒
    ev_SS (S (S n)) (ev_SS n H).
-/

def even_add_four' : ∀n, even n → even (n + 4) := λn h, ev_ss (ev_ss h)

/-
Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).
Check ev_plus4''.
-/

def even_add_four'' (n) (h : even n) : even (n + 4) := ev_ss (ev_ss h)

/-
Definition ev_plus2 : Prop :=
  ∀n, ∀(E : even n), even (n + 2).
-/

def even_add_two : Prop := ∀n, ∀e : even n, even (n + 2)

/-
Definition ev_plus2' : Prop :=
  ∀n, ∀(_ : even n), even (n + 2).
-/

def even_add_two' : Prop := ∀n, ∀_ : even n, even (n + 2)

/-
Definition ev_plus2'' : Prop :=
  ∀n, even n → even (n + 2).
-/

def even_add_two'' : Prop := ∀n, even n → even (n + 2)

/-
Definition add1 : nat → nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)
-/

def add_one : nat → nat :=
begin
  intro n,
  apply succ,
  exact n,
end

#print add_one

#reduce add_one 2

/-
Inductive and (P Q : Prop) : Prop :=
| conj : P → Q → and P Q.
End And.
-/

structure and (P Q : Prop) : Prop := intro :: (left : P) (right : Q)

/-
Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)
-/

#print and
#print prod

/-
Lemma and_comm : ∀P Q : Prop, P ∧ Q ↔ Q ∧ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.
-/

lemma and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
begin
  split,
    rintro ⟨p, q⟩,
    exact ⟨q, p⟩,
  rintro ⟨q, p⟩,
  exact ⟨p, q⟩,
end

/-
Definition and_comm'_aux P Q (H : P ∧ Q) : Q ∧ P :=
  match H with
  | conj HP HQ ⇒ conj HQ HP
  end.

Definition and_comm' P Q : P ∧ Q ↔ Q ∧ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).
-/

def and_comm'_aux : P ∧ Q → Q ∧ P
| ⟨p, q⟩ := ⟨q, p⟩

def and_comm' : P ∧ Q ↔ Q ∧ P := ⟨and_comm'_aux, and_comm'_aux⟩

/-
Definition conj_fact : ∀P Q R, P ∧ Q → Q ∧ R → P ∧ R
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def conj_fact (hpq : P ∧ Q) (hqr : Q ∧ R) : P ∧ R := ⟨hpq.left, hqr.right⟩

/-
Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P → or P Q
| or_intror : Q → or P Q.

End Or.
-/

namespace or

inductive or (P Q : Prop) : Prop
| inl : P → or
| inr : Q → or

end or

/-
Definition or_comm : ∀P Q, P ∨ Q → Q ∨ P
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def or_comm : P ∨ Q → Q ∨ P
| (or.inl p) := or.inr p
| (or.inr q) := or.inl q

/-
Module Ex.

Inductive ex {A : Type} (P : A → Prop) : Prop :=
| ex_intro : ∀x : A, P x → ex P.

End Ex.
-/

namespace Exists

inductive Exists (P : α → Prop) : Prop
| intro : ∀x, P x → Exists

/-
Check ex (fun n ⇒ even n).
(* ===> exists n : nat, even n
        : Prop *)
-/

#check Exists (λn, even n)

end Exists

/-
Definition some_nat_is_even : ∃n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).
-/

def some_nat_is_even : ∃n, even n := Exists.intro 4 (ev_ss (ev_ss ev_0))

/-
Definition ex_ev_Sn : ex (fun n ⇒ even (S n))
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def ex_even_succ : ∃n, even (succ n) := Exists.intro 1 (ev_ss ev_0)

/-
Inductive True : Prop :=
  | I : True.
-/

inductive true : Prop
| intro : true

/-
Inductive False : Prop := .
-/

inductive false : Prop

/-
Module MyEquality.

Inductive eq {X:Type} : X → X → Prop :=
| eq_refl : ∀x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.
-/

#check eq

inductive eq (a : α) : α → Prop
| refl : eq a

local infix == := eq

/-
Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.
-/

lemma four : 2 + 2 == 1 + 3 := by apply eq.refl

/-
Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : ∀(X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) ⇒ eq_refl [x].
-/

def four' : 2 + 2 == 1 + 3 := eq.refl

def singleton (a : α) : [] ++ [a] == a::[] := eq.refl

/-
Lemma equality__leibniz_equality : ∀(X : Type) (x y: X),
  x == y → ∀P:X→Prop, P x → P y.
Proof.
(* FILL IN HERE *) Admitted.
-/

lemma equality__leibniz_equality
  (heq : x == y) (P : α → Prop) (h : P x) : P y :=
begin
  cases heq,
  exact h,
end

/-
Lemma leibniz_equality__equality : ∀(X : Type) (x y: X),
  (∀P:X→Prop, P x → P y) → x == y.
Proof.
(* FILL IN HERE *) Admitted.
-/

lemma leibniz_equality__equality (h : ∀P : α → Prop, P x → P y) : x == y :=
begin
  apply h,
  exact eq.refl,
end

#print leibniz_equality__equality

end proofobjects