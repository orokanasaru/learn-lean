import tactic.basic
import .ch07_indprop

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

open even
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

#print ev_4

/-
Check (ev_SS 2 (ev_SS 0 ev_0)).
(* ===> even 4 *)
-/

#check ev_ss 2 (ev_ss 0 ev_0)

/-
Theorem ev_4': even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.
-/

#print ev_4'

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

theorem ev_4'' : even 4 :=
begin
  trace_state,
  apply ev_ss,
  trace_state,
  apply ev_ss,
  trace_state,
  apply ev_0,
  trace_state,
end

/- goofing off a bit -/

theorem ev_4''' : even 4 :=
by repeat { constructor, }


/-
Definition ev_4''' : even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).
-/

/- yeah, '' was made this way -/
def ev_4'''' : even 4 := ev_ss 2 (ev_ss 0 ev_0)

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

#print ev_4
#print ev_4'
#print ev_4''
#print ev_4'''

/-
Theorem ev_8 : even 8.
Proof.
  (* FILL IN HERE *) Admitted.

Definition ev_8' : even 8
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

theorem ev_8 : even 8 := by { repeat {constructor, }, }

def ev_8' : even 8 := ev_ss _ (ev_ss _ (ev_ss _ (ev_ss _ ev_0)))

/-
Theorem ev_plus4 : ∀n, even n → even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.
-/

#print ev_plus4

/-
Definition ev_plus4' : ∀n, even n → even (4 + n) :=
  fun (n : nat) ⇒ fun (H : even n) ⇒
    ev_SS (S (S n)) (ev_SS n H).
-/

open nat

/-
lean treats succ n as n + 1.
dealing with basic things like symmetry is not fun
-/

def ev_plus4' : ∀n, even n → even (n + 4) :=
  λn h, (ev_ss (succ (succ n)) (ev_ss n h))

/-
Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).
Check ev_plus4''.
-/

def ev_plus4'' (n) (h : even n) : even (n + 4) :=
  ev_ss (succ (succ n)) (ev_ss n h)

/-
Definition ev_plus2 : Prop :=
  ∀n, ∀(E : even n), even (n + 2).
-/

def ev_plus2 : Prop := ∀n, ∀e : even n, even (n + 2)

/-
Definition ev_plus2' : Prop :=
  ∀n, ∀(_ : even n), even (n + 2).
-/

def ev_plus2' : Prop := ∀n, ∀_ : even n, even (n + 2)

/-
Definition ev_plus2'' : Prop :=
  ∀n, even n → even (n + 2).
-/

def ev_plus2'' : Prop := ∀n, even n → even (n + 2)

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

def add1 : nat → nat :=
begin
  intro n,
  apply succ,
  apply n,
end

#print add1

#reduce add1 2

/-
Inductive and (P Q : Prop) : Prop :=
| conj : P → Q → and P Q.
End And.
-/

inductive and' (P Q : Prop) : Prop
| conj : P → Q → and'

/-
Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)
-/

#print and'
#print poly.prod'

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

lemma and_comm' (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
begin
  split,
    intro h,
    cases h with hp hq,
    split,
      exact hq,
    exact hp,
  intro h,
  cases h with hq hp,
  split,
    exact hp,
  exact hq,
end

/-
Definition and_comm'_aux P Q (H : P ∧ Q) : Q ∧ P :=
  match H with
  | conj HP HQ ⇒ conj HQ HP
  end.

Definition and_comm' P Q : P ∧ Q ↔ Q ∧ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).
-/

def and_comm'_aux {P Q} : P ∧ Q → Q ∧ P
| (and.intro p q) := and.intro q p

def and_comm'_aux' {P Q} : P ∧ Q → Q ∧ P
| ⟨p, q⟩ := ⟨q, p⟩

def and_comm'' (P Q) : P ∧ Q ↔ Q ∧ P :=
  ⟨@and_comm'_aux P Q, @and_comm'_aux Q P⟩

/-
Definition conj_fact : ∀P Q R, P ∧ Q → Q ∧ R → P ∧ R
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def conj_fact {P Q R} (hpq : P ∧ Q) (hqr : Q ∧ R) : P ∧ R
  := ⟨hpq.left, hqr.right⟩

/-
Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P → or P Q
| or_intror : Q → or P Q.

End Or.
-/

inductive or' (P Q : Prop) : Prop
| or_introl : P → or'
| or_intror : Q → or'

/-
Definition or_comm : ∀P Q, P ∨ Q → Q ∨ P
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def or_comm' {P Q} : P ∨ Q → Q ∨ P
| (or.inl p) := or.inr p
| (or.inr q) := or.inl q

def or_comm'' {P Q} (h : P ∨ Q) : Q ∨ P
  := or.elim h or.inr or.inl

/-
Module Ex.

Inductive ex {A : Type} (P : A → Prop) : Prop :=
| ex_intro : ∀x : A, P x → ex P.

End Ex.
-/

inductive ex {α : Type} (P : α → Prop) : Prop
| ex_intro : ∀x, P x → ex

open ex

/-
Check ex (fun n ⇒ even n).
(* ===> exists n : nat, even n
        : Prop *)
-/

#check Exists (λ n, even n)

/-
Definition some_nat_is_even : ∃n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).
-/

def some_nat_is_even : ∃n, even n :=
  Exists.intro 4 (ev_ss 2 (ev_ss 0 ev_0))

def some_nat_is_even' : ∃n, even n :=
  ⟨4, ev_ss 2 (ev_ss 0 ev_0)⟩

/-
Definition ex_ev_Sn : ex (fun n ⇒ even (S n))
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def ex_ev_Sn : ex (λ n, even (succ n))
  := ex_intro 1 (ev_ss _ ev_0)

def ex_ev_Sn' : ex (λ n, even (succ n))
  := ⟨1, ev_ss _ ev_0⟩

/-
Inductive True : Prop :=
  | I : True.
-/

inductive True : Prop
| I : True

/-
Inductive False : Prop := .
-/

inductive False : Prop

/-
Module MyEquality.

Inductive eq {X:Type} : X → X → Prop :=
| eq_refl : ∀x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.
-/

inductive eq' {α} : α → α → Prop
| eq_refl (x) : eq' x x

open eq'

section
local infix ` == ` := eq'

lemma four : 2 + 2 == 1 + 3 := by apply eq_refl
end

/-
Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : ∀(X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) ⇒ eq_refl [x].
-/

def four' : 2 + 2 == 1 + 3 := heq.refl _

def singleton' {α} (a : α) : []++[a] == a::[] := heq.refl _

/-
Lemma equality__leibniz_equality : ∀(X : Type) (x y: X),
  x == y → ∀P:X→Prop, P x → P y.
Proof.
(* FILL IN HERE *) Admitted.
-/

lemma equality__leibniz_equality {α} {x y}
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

/-
TODO - leibniz_equality
-/