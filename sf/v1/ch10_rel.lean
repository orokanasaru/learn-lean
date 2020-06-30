import tactic.basic
import .ch07_indprop

open nat (
  le less_than_or_equal.refl less_than_or_equal.step lt
)

open indprop (next_nat total_relation total_relation.intro)
open indprop.next_nat

variables {α : Type}
variables {n m o p: ℕ}

namespace rel

/-
Definition relation (X: Type) := X → X → Prop.
-/

def relation (α : Type) := α → α → Prop

/-
Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)

Check le : nat → nat → Prop.
Check le : relation nat.
-/

#print le

#check (le : ℕ → ℕ → Prop)
#check (le : relation ℕ)

/-
Definition partial_function {X: Type} (R: relation X) :=
  ∀x y1 y2 : X, R x y1 → R x y2 → y1 = y2.
-/

def partial_function (R : relation α) :=
  ∀{x y₁ y₂} (h₁ : R x y₁) (h₂ : R x y₂), y₁ = y₂

/-
Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop :=
           nn : next_nat n (S n) *)

Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. Qed.
-/

#print next_nat

#check (next_nat : relation ℕ)

theorem next_nat_partial_function : partial_function next_nat :=
begin
  unfold partial_function,
  intros,
  cases h₁,
  cases h₂,
  refl,
end

/-
Theorem le_not_a_partial_function :
  ¬(partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. Qed.
-/

theorem le_not_a_partial_function : ¬partial_function le :=
begin
  unfold partial_function,
  by_contradiction c,
  have nonsense : 0 = 1,
    apply @c 0 0 1,
      apply less_than_or_equal.refl,
    apply less_than_or_equal.step,
    apply less_than_or_equal.refl,
  cases nonsense,
end

theorem total_relation_not_partial : ¬partial_function total_relation :=
begin
  unfold partial_function,
  by_contradiction c,
  cases c (total_relation.intro 0 0) (total_relation.intro 0 1),
end

theorem empty_relation_partial : partial_function (@empty_relation α) :=
begin
  unfold partial_function,
  intros,
  cases h₁,
end

/-
Definition reflexive {X: Type} (R: relation X) :=
  ∀a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.
-/

def reflexive (R : relation α) := ∀a, R a a

theorem le_refl : reflexive le :=
begin
  unfold reflexive,
  intro n,
  apply less_than_or_equal.refl,
end

/-
Definition transitive {X: Type} (R: relation X) :=
  ∀a b c : X, (R a b) → (R b c) → (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo. Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.
-/

#check transitive

def transitive (R : relation α) :=
  ∀{a b c : α} (hab : R a b) (hbc : R b c), R a c

theorem le_trans: transitive le :=
begin
  unfold transitive,
  intros,
  induction hbc with b' h ih,
    exact hab,
  apply less_than_or_equal.step,
  exact ih,
end

theorem lt_trans : transitive lt :=
begin
  unfold transitive,
  intros,
  exact le_trans (less_than_or_equal.step hab) hbc,
end

/-
Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* FILL IN HERE *) Admitted.
-/

theorem lt_trans' : transitive lt :=
begin
  unfold transitive,
  intros,
  induction hbc with b' h ih,
    exact less_than_or_equal.step hab,
  exact less_than_or_equal.step ih,
end

/-
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* FILL IN HERE *) Admitted.
-/

theorem lt_trans'' : transitive lt :=
begin
  unfold transitive,
  intros,
  induction c with c ih,
    cases hbc,
  cases hbc with _ h,
    exact less_than_or_equal.step hab,
  exact less_than_or_equal.step (ih h),
end

/-
Theorem le_Sn_le : ∀n m, S n ≤ m → n ≤ m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.
-/

theorem nat.le_of_succ_le (h : n + 1 ≤ m) : n ≤ m :=
begin
  apply le_trans,
    apply less_than_or_equal.step,
    apply less_than_or_equal.refl,
  exact h,
end

/-
Theorem le_S_n : ∀n m,
  (S n ≤ S m) → (n ≤ m).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem nat.le_of_succ_le_succ (h : n + 1 ≤ m + 1) : n ≤ m :=
begin
  cases h with _ h,
    exact less_than_or_equal.refl,
  exact nat.le_of_succ_le h,
end

/-
Theorem le_Sn_n : ∀n,
  ¬(S n ≤ n).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem nat.not_succ_le_self (n) : ¬(n + 1 ≤ n) :=
begin
  by_contra c,
  induction n with n ih,
    cases c,
  exact ih (nat.le_of_succ_le_succ c),
end

/-
Definition symmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) → (R b a).
-/

def symmetric (R : relation α) := ∀{a b : α} (h : R a b), R b a

/-
Theorem le_not_symmetric :
  ¬(symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem le_not_symmetric : ¬symmetric le :=
begin
  unfold symmetric,
  by_contra c,
  cases c (less_than_or_equal.step (@less_than_or_equal.refl 0)),
end

/-
Definition antisymmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) → (R b a) → a = b.
-/

def anti_symmetric (R : relation α) := ∀{a b} (hab : R a b) (hba : R b a), a = b

/-
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem le_antisymm : anti_symmetric le :=
begin
  unfold anti_symmetric,
  intros,
  induction a with a ih generalizing b,
    cases hba,
    refl,
  cases b,
    cases hab,
  apply congr_arg,
  apply ih,
    exact nat.le_of_succ_le_succ hab,
  exact nat.le_of_succ_le_succ hba,
end

/-
Theorem le_step : ∀n m p,
  n < m →
  m ≤ S p →
  n ≤ p.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem le_step (hn : n < m) (hm : m ≤ p + 1) : n ≤ p :=
  nat.le_of_succ_le_succ $ le_trans hn hm

/-
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) ∧ (symmetric R) ∧ (transitive R).
-/

def equivalence (R : relation α) := reflexive R ∧ symmetric R ∧ transitive R

/-
Definition order {X:Type} (R: relation X) :=
  (reflexive R) ∧ (antisymmetric R) ∧ (transitive R).
-/

def partial_order (R : relation α) :=
  reflexive R ∧ anti_symmetric R ∧ transitive R

/-
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) ∧ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans. Qed.
-/

def preorder (R : relation α) := reflexive R ∧ transitive R

theorem le_order : partial_order le :=
begin
  unfold partial_order,
  split,
    apply le_refl,
  split,
    apply le_antisymm,
  apply le_trans,
end

/-
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.
-/

inductive clos_refl_trans (R : relation α) : relation α
| rt_step {x y} (h : R x y) : clos_refl_trans x y
| rt_refl (x) : clos_refl_trans x x
| rt_trans {x y z}
  (hxy : clos_refl_trans x y)
  (hyz : clos_refl_trans y z) : clos_refl_trans x z

open clos_refl_trans

/-
Theorem next_nat_closure_is_le : ∀n m,
  (n ≤ m) ↔ ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.
-/

theorem next_nat_closure_is_le : n ≤ m ↔ (clos_refl_trans next_nat) n m :=
begin
  split,
    intro h,
    induction h with m h ih,
      apply rt_refl,
    apply rt_trans,
    apply ih,
      apply rt_step,
    apply nn,
  intro h,
  induction h,
    case rt_step : x y h {
      cases h,
      apply less_than_or_equal.step,
      exact less_than_or_equal.refl,
    },
  case rt_refl : x { exact less_than_or_equal.refl, },
  case rt_trans : x y z hxy hyz ihx ihy { exact le_trans ihx ihy, },
end

/-
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A → Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.
-/

inductive clos_refl_trans_1n (R : relation α) : α → α → Prop
| rt1n_refl (x) : clos_refl_trans_1n x x
| rt1n_trans {x y z} (hxy : R x y) (hyz : clos_refl_trans_1n y z)
  : clos_refl_trans_1n x z

open clos_refl_trans_1n

/-
Lemma rsc_R : ∀(X:Type) (R:relation X) (x y : X),
       R x y → clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.
-/

lemma rsc_R {R : relation α} {x y} (h : R x y) : clos_refl_trans_1n R x y
  := rt1n_trans h (rt1n_refl y)

/-
Lemma rsc_trans :
  ∀(X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y →
      clos_refl_trans_1n R y z →
      clos_refl_trans_1n R x z.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma rsc_trans {R : relation α} {x y z}
  (hxy : clos_refl_trans_1n R x y) (hyz : clos_refl_trans_1n R y z)
  : clos_refl_trans_1n R x z :=
begin
  induction hxy,
  case rt1n_refl { exact hyz, },
  case rt1n_trans : x' y' z' hxy' hyz' ih { exact rt1n_trans hxy' (ih hyz), },
end

/-
Theorem rtc_rsc_coincide :
         ∀(X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y ↔ clos_refl_trans_1n R x y.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem rtc_rsc_coincide {R : relation α} {x y}
  : clos_refl_trans R x y ↔ clos_refl_trans_1n R x y :=
begin
  split,
    intro h,
    induction h,
    case rt_step : x' y' h' { exact rsc_R h', },
    case rt_refl { exact rt1n_refl h, },
    case rt_trans : x' y' z' hxy hyz ihy ihz { exact rsc_trans ihy ihz, },
  intro h,
  induction h,
  case rt1n_refl { exact rt_refl h },
  case rt1n_trans : x' y' z' hxy hyz ih { exact rt_trans (rt_step hxy) ih, },
end

end rel