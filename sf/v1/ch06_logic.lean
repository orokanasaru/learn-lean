import tactic.basic
import .ch05_tactics

/-
Check 3 = 3.
(* ===> Prop *)
Check ∀n m : nat, n + m = m + n.
(* ===> Prop *)
-/

#check 3 = 3

#check ∀ n m : ℕ, n + m
= m + n

/-
Check 2 = 2.
(* ===> Prop *)
Check ∀n : nat, n = 2.
(* ===> Prop *)
Check 3 = 4.
(* ===> Prop *)
-/

#check 2 = 2

#check ∀ n : ℕ, n = 2

#check 3 = 4

/-
Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.
-/

theorem plus_2_2_is_4 : 2 + 2 = 4 := rfl

/-
Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)
-/

@[simp]
def plus_fact : Prop := 2 + 2 = 4

#check plus_fact

/-
Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.
-/

theorem plus_fact_is_true : plus_fact := by simp

/-
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)
-/

def is_three (n : ℕ) : Prop := n = 3

#check is_three

/-
Definition injective {A B} (f : A → B) :=
  ∀x y : A, f x = f y → x = y.
Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.
-/

def injective {α β : Type} (f : α → β)
  :=  ∀ (x y: α), f x = f y → x = y

lemma succ_inj : injective nat.succ :=
begin
  intros n m h,
  injection h,
end

/-
Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)
-/

#check @eq

/-
Example and_example : 3 + 4 = 7 ∧ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by split; refl

/-
Lemma and_intro : ∀A B : Prop, A → B → A ∧ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.
-/

/- in core as and.intro -/

lemma and_intro (α β : Prop) (a : α) (b : β) : α ∧ β :=
  by split; simp *

/-
Example and_example' : 3 + 4 = 7 ∧ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by apply and_intro; refl

/-
Example and_exercise :
  ∀n m : nat, n + m = 0 → n = 0 ∧ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma and_exercise : ∀ (n m : ℕ) (h : n + m = 0), n = 0 ∧ m = 0
| 0 0 := by intros; split; refl
| (n + 1) m :=
begin
  intros,
  rw [add_comm, ←add_assoc] at h,
  contradiction,
end
| n (m + 1) :=
begin
  intros,
  rw [←add_assoc] at h,
  contradiction,
end

/-
Lemma and_example2 :
  ∀n m : nat, n = 0 ∧ m = 0 → n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
-/

lemma and_example2 (n m : ℕ) (h : n = 0 ∧ m = 0)
  : n + m = 0 := by cases h; simp *

/-
Lemma and_example2' :
  ∀n m : nat, n = 0 ∧ m = 0 → n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
-/

/- not sure how to do this in lean -/

/-
Lemma and_example2'' :
  ∀n m : nat, n = 0 → m = 0 → n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
-/

lemma and_example2'' (n m : ℕ) (hn : n = 0) (hm : m = 0)
  : n + m = 0 := by simp *

/-
Lemma and_example3 :
  ∀n m : nat, n + m = 0 → n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 ∧ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.
-/

lemma and_example3 (n m : ℕ) (h : n + m = 0) : n * m = 0 :=
begin
  have h : n = 0 ∧ m = 0,
    exact and_exercise n m h,
  cases h with hn hm,
  rw hn,
  simp,
end

/-
Lemma proj1 : ∀P Q : Prop,
  P ∧ Q → P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.
-/

lemma proj1 (p q : Prop) (h : p ∧ q) : p := by simp *

/-
Lemma proj2 : ∀P Q : Prop,
  P ∧ Q → Q.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma proj2 (p q : Prop) (h : p ∧ q) : q := by exact h.right

/-
Theorem and_commut : ∀P Q : Prop,
  P ∧ Q → Q ∧ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.
-/

theorem and_commut (p q : Prop) (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

/-
Theorem and_assoc : ∀P Q R : Prop,
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* FILL IN HERE *) Admitted.
-/

theorem and_assoc' (p q r : Prop) (h : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r := ⟨⟨h.left, h.right.left⟩, h.right.right⟩

/-
Check and.
(* ===> and : Prop -> Prop -> Prop *)
-/

#check @and

/-
Lemma or_example :
  ∀n m : nat, n = 0 ∨ m = 0 → n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.
-/

lemma or_example (n m : ℕ) (h : n = 0 ∨ m = 0) : n * m = 0 :=
  by cases h; simp *

/-
Lemma or_intro : ∀A B : Prop, A → A ∨ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.
-/

lemma or_intro (α β : Prop) (a : α) : α ∨ β :=
  by left; simp *

/-
Lemma zero_or_succ :
  ∀n : nat, n = 0 ∨ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.
-/

open nat

/- i assume the coq version above doesn't work -/

lemma zero_or_succ : ∀ (n : ℕ), n = 0 ∨ n = succ (pred n)
| 0 := by left; refl
| (n + 1) := by right; refl

/-
Module MyNot.

Definition not (P:Prop) := P → False.

Notation "¬x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.
-/

section my_not

def not' (p : Prop) := p → false

local prefix `¬` := not'

#check not'

end my_not

/-
Theorem ex_falso_quodlibet : ∀(P:Prop),
  False → P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.
-/

theorem ex_false_quodlibet (p : Prop) (f : false) : p
  := by contradiction

/-
Fact not_implies_our_not : ∀(P:Prop),
  ¬P → (∀(Q:Prop), P → Q).
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma not_implies_our_not (p : Prop) (h : ¬p) (q : Prop)
  : p → q :=
begin
  intro p,
  contradiction,
end

/-
Notation "x ≠ y" := (~(x = y)).
-/

section
local infix ` != `:50 := λ x y, ¬(x = y)
end

/-
Theorem zero_not_one : 0 ≠ 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.
-/

/- can't unfold not -/

theorem zero_not_one : 0 ≠ 1 := by simp

/-
Theorem not_False :
  ¬False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : ∀P Q : Prop,
  (P ∧ ¬P) → Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : ∀P : Prop,
  P → ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.
-/

/- as defined in core -/
theorem not_false' : ¬false := id

theorem contradiction_implies_anything
  (p q : Prop) (h : p ∧ ¬p) : q := by cases h; contradiction

theorem double_neg (p : Prop) (h : p) : ¬¬p :=
by by_contra; contradiction

/-
Theorem contrapositive : ∀(P Q : Prop),
  (P → Q) → (¬Q → ¬P).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem contrapositive (p q : Prop) (h: p → q)
  : (¬q → ¬p) :=
begin
  intro hnq,
  assume p,
  /- i totally forgot this style works -/
  have q,
    exact h p,
  contradiction,
end

/-
Theorem not_both_true_and_false : ∀P : Prop,
  ¬(P ∧ ¬P).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem not_both_true_and_false (p : Prop) :
  ¬(p ∧ ¬p) :=
begin
  by_contra h,
  cases h,
  contradiction,
end

/-
Theorem not_true_is_false : ∀b : bool,
  b ≠ true → b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.
-/

/-
the inability to unfold not is a constant pita
bool and prop having different values for t/f also is

i've yet to find a case where exfalso doesn't just
destroy all necessary info
-/

theorem not_true_is_false (b : bool) (h : b ≠ true)
  : b = false := by simp * at *

/-
Theorem not_true_is_false' : ∀b : bool,
  b ≠ true → b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.
-/

/-
yeah, still somewhere between unpleasant and
impossible in lean
-/

/-
Lemma True_is_true : True.
Proof. apply I. Qed.
-/

lemma True_is_true : tt := by simp

/-
Module MyIff.

Definition iff (P Q : Prop) := (P → Q) ∧ (Q → P).

Notation "P ↔ Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : ∀P Q : Prop,
  (P ↔ Q) → (Q ↔ P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.

Lemma not_true_iff_false : ∀b,
  b ≠ true ↔ b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.
-/

section

def iff' (p q : Prop) := p → q ∧ q → p

local infix ↔ := iff'

end

theorem iff_sym (p q : Prop) (h : p ↔ q) : q ↔ p :=
begin
  cases h with hpq hqp,
  split,
    exact hqp,
  exact hpq,
end

lemma not_true_iff_false (b: bool) : b ≠ tt ↔ b = ff :=
  by split; simp

/-
Theorem or_distributes_over_and : ∀P Q R : Prop,
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem or_distributes_over_and (p q r : Prop) :
  p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
begin
  split; intro h,
    cases h with hp hqr,
      split; exact or.inl hp,
    split,
      exact or.inr hqr.left,
    exact or.inr hqr.right,
  cases h with hpq hpr,
  cases hpq with hp hq,
    exact or.inl hp,
  cases hpr with hp hr,
    exact or.inl hp,
  exact or.inr ⟨hq, hr⟩
end

/-
Lemma mult_0 : ∀n m, n * m = 0 ↔ n = 0 ∨ m = 0.

Lemma or_assoc :
  ∀P Q R : Prop, P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R.
-/

lemma mult_0 (n m : ℕ) :
  n * m = 0 ↔ n = 0 ∨ m = 0 :=
begin
  split,
   exact eq_zero_of_mul_eq_zero,
  apply or_example,
end

lemma or_assoc' (p q r : Prop) :
  p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r :=
begin
  split; intro h,
    cases_type* or,
        exact or.inl (or.inl h),
      exact or.inl (or.inr h),
    exact or.inr h,
  cases_type* or,
      exact or.inl h,
    exact or.inr (or.inl h),
  exact or.inr (or.inr h),
end

/-
Lemma mult_0_3 :
  ∀n m p, n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.
-/

lemma mult_0_3 (n m p : ℕ) :
  n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 :=
begin
  repeat { rewrite mult_0 },
  rewrite or_assoc,
end

/-
Lemma apply_iff_example :
  ∀n m : nat, n * m = 0 → n = 0 ∨ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.
-/

/- apply doesn't seem to work with iff in lean -/
/- can use mp/mpr to pick a direction -/

lemma apply_iff_example (n m : ℕ) :
  n * m = 0 → n = 0 ∨ m = 0 := (mult_0 n m).mp

/-
Lemma four_is_even : ∃n : nat, 4 = n + n.
Proof.
  ∃2. reflexivity.
Qed.
-/

lemma four_is_even : ∃n : ℕ, 4 = n + n := ⟨2, rfl⟩

/-
Theorem exists_example_2 : ∀n,
  (∃m, n = 4 + m) →
  (∃o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  ∃(2 + m).
  apply Hm. Qed.
-/

theorem exists_example_2 (n : ℕ) (h : ∃ m, n = 4 + m) :
  ∃ o, n = 2 + o :=
begin
  cases h with m hm,
  /-
  i'm sure there's a nicer way
  possibly involving calc
  -/
  exact ⟨m + 2, begin
    rw add_comm m,
    rw ←add_assoc,
    exact hm,
  end⟩
end

/-
Theorem dist_not_exists : ∀(X:Type) (P : X → Prop),
  (∀x, P x) → ¬(∃x, ¬P x).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem dist_not_exists {α : Type} (p : α → Prop) (h : ∀x, p x)
  : ¬(∃x, ¬p x) :=
begin
  by_contra he,
  cases he with a hnp,
  have hp, exact h a,
  contradiction,
end

/-
Theorem dist_exists_or : ∀(X:Type) (P Q : X → Prop),
  (∃x, P x ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
-/

theorem dist_exists_or {α : Type} (p q : α → Prop) :
  (∃a, p a ∨ q a) ↔ (∃a, p a) ∨ (∃a, q a) :=
begin
  split; intro,
    cases a with a h,
    cases h with hp hq,
      exact or.inl ⟨a, hp⟩,
    exact or.inr ⟨a, hq⟩,
  cases a with hp hq,
    cases hp with a hp,
    exact ⟨a, or.inl hp⟩,
  cases hq with a hq,
  exact ⟨a, or.inr hq⟩,
end

/-
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] ⇒ False
  | x' :: l' ⇒ x' = x ∨ In x l'
  end.
-/

@[simp]
def In {α : Type} (a : α) : list α → Prop
| [] := false
| (h::t) := h = a ∨ In t

/-
Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  ∀n, In n [2; 4] →
  ∃n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - ∃1. rewrite <- H. reflexivity.
  - ∃2. rewrite <- H. reflexivity.
Qed.
-/

example : In 4 [1,2,3,4,5] := by simp

example (n : ℕ) (h : In n [2, 4]) : ∃n', n = 2 * n' :=
begin
  simp at h,
  cases h,
    exact ⟨1, by rw ←h; refl⟩,
  exact ⟨2, by rw ←h; refl⟩
end

/-
Lemma In_map :
  ∀(A B : Type) (f : A → B) (l : list A) (x : A),
    In x l →
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.
-/

open list

lemma in_map {α β : Type}
  (f : α → β) (l : list α) (a : α) (h : In a l)
  : In (f a) (map f l) :=
begin
  induction l with h t ih,
    simp at h,
    contradiction,
  simp at *,
  cases h with hl hr,
    left,
    rw hl,
  right,
  exact ih hr,
end

/-
Lemma In_map_iff :
  ∀(A B : Type) (f : A → B) (l : list A) (y : B),
    In y (map f l) ↔
    ∃x, f x = y ∧ In x l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma in_map_iff {α β : Type}
  (f : α → β) (l : list α) (b : β)
  : In b (map f l) ↔ ∃a, f a = b ∧ In a l :=
begin
  split; intro h,
    induction l with h t ih; simp at h,
      contradiction,
    cases h with hl hr,
      have hr : In h (h :: t),
        simp,
      exact ⟨h, hl, hr⟩,
    have ih, exact ih hr,
    cases ih with a ih,
    cases ih with ihl ihr,
    have ihr : In a (h::t),
      simp,
      exact or.inr ihr,
    exact ⟨a, ihl, ihr⟩,
  cases h with a h,
  induction l with h t ih; simp at h,
    contradiction,
  simp,
  cases h with hl hr,
  cases hr,
    rw hr,
    exact or.inl hl,
  exact or.inr (ih ⟨hl, hr⟩),
end

/-
Lemma In_app_iff : ∀A l l' (a:A),
  In a (l++l') ↔ In a l ∨ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma in_app_iff {α : Type} (l l' : list α) (a : α) :
  In a (l ++ l') ↔ In a l ∨ In a l' :=
begin
  split; intro h,
    induction l with hl tl ih; simp at h,
      exact or.inr h,
    cases h with hl hr,
      simp,
      exact or.inl (or.inl hl),
    have ih, exact ih hr,
    cases ih with ihl ihr,
      simp,
      exact or.inl (or.inr ihl),
    exact or.inr ihr,
  cases h,
    induction l with h t ih; simp at h,
      contradiction,
    simp,
    cases h with hl hr,
      exact or.inl hl,
    exact or.inr (ih hr),
  induction l' with h t ih generalizing l; simp at h,
    contradiction,
  cases h with hl hr; induction l with hl tl ihl; simp,
        exact or.inl hl,
      exact or.inr ihl,
    exact or.inr hr,
  exact or.inr ihl,
end

/-
Fixpoint All {T : Type} (P : T → Prop) (l : list T) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma All_In :
  ∀T (P : T → Prop) (l : list T),
    (∀x, In x l → P x) ↔
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- hint remember def for in -/

@[simp]
def all {α : Type} (p : α → Prop) : list α → Prop
| [] := true
| (h::t) := p h ∧ all t

lemma all_in {α : Type} (p : α → Prop) (l : list α)
  : (∀ a, In a l → p a) ↔ all p l :=
begin
  split; intro h; induction l with hd t ih; simp at h; simp,
    split,
      apply h,
      simp,
    apply ih,
    intros a i,
    exact h a (or.inr i),
  intros a i,
  cases i,
    rw i at h,
    exact h.left,
  exact ih h.right a i,
end

/-
Definition combine_odd_even (Podd Peven : nat → Prop) : nat → Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

/-
either i super missed the mark with this def
or this is not a three star problem
-/

@[simp]
def combine_odd_even (podd peven : ℕ → Prop) (n : ℕ) : Prop :=
  if oddb n then podd n else peven n

/-
Theorem combine_odd_even_intro :
  ∀(Podd Peven : nat → Prop) (n : nat),
    (oddb n = true → Podd n) →
    (oddb n = false → Peven n) →
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  ∀(Podd Peven : nat → Prop) (n : nat),
    combine_odd_even Podd Peven n →
    oddb n = true →
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  ∀(Podd Peven : nat → Prop) (n : nat),
    combine_odd_even Podd Peven n →
    oddb n = false →
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem combine_odd_even_intro
  (podd peven : ℕ → Prop) (n : ℕ)
  (hodd : oddb n = true → podd n)
  (heven : oddb n = false → peven n)
  : combine_odd_even podd peven n :=
begin
  simp at *,
  cases (evenb n); simp *,
end

theorem combine_odd_even_elim_odd
  (podd peven : ℕ → Prop) (n : ℕ)
  (h : combine_odd_even podd peven n)
  (hodd : oddb n = true)
  : podd n := by cases (evenb n); simp * at *

theorem combine_odd_even_elim_even
  (podd peven : ℕ → Prop) (n : ℕ)
  (h : combine_odd_even podd peven n)
  (heven : oddb n = false)
  : peven n := by cases (evenb n); simp * at *

/-
Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)
-/

/- yay metavariables -/
#check add_comm

/-
Lemma plus_comm3 :
  ∀x y z, x + (y + z) = (z + y) + x.
Proof.
  (* WORKED IN CLASS *)
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.
-/

-- lemma plus_comm3 (x y z : ℕ)
--   : x + (y + z) = (z + y) + x :=
-- begin
--   rw add_comm,
--   rw add_comm,
--   sorry
-- end

/-
Lemma plus_comm3_take2 :
  ∀x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.
-/

lemma plus_comm3_take2 (x y z : ℕ)
  : x + (y + z) = (z + y) + x :=
begin
  rw add_comm,
  have h : y + z = z + y,
    rw add_comm,
  rw h,
end

/-
Lemma plus_comm3_take3 :
  ∀x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.
-/

lemma plus_comm3_take3 (x y z : ℕ)
  : x + (y + z) = (z + y) + x :=
begin
  rw add_comm,
  /- i assume partial app works in coq as well -/
  rw add_comm y,
end

lemma in_not_nil {α : Type} (a : α) (l : list α) (h : In a l)
  : l ≠ [] :=
begin
  cases l with hd t,
    simp at h,
    contradiction,
  simp,
end

/-
Lemma in_not_nil_42 :
  ∀l : list nat, In 42 l → l ≠ [].
Proof.
  (* WORKED IN CLASS *)
  intros l H.
  Fail apply in_not_nil.
Abort.
(* apply ... with ... *)

Lemma in_not_nil_42_take2 :
  ∀l : list nat, In 42 l → l ≠ [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.
(* apply ... in ... *)

Lemma in_not_nil_42_take3 :
  ∀l : list nat, In 42 l → l ≠ [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.
(* Explicitly apply the lemma to the value for x. *)

Lemma in_not_nil_42_take4 :
  ∀l : list nat, In 42 l → l ≠ [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.
(* Explicitly apply the lemma to a hypothesis. *)

Lemma in_not_nil_42_take5 :
  ∀l : list nat, In 42 l → l ≠ [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.
-/

-- lemma in_not_nil_42 (l : list ℕ) (h : In 42 l)
--   : l ≠ [] :=
-- begin
--   apply in_not_nil,
--   sorry
-- end

lemma in_not_nil_42_take2 (l : list ℕ) (h : In 42 l)
  : l ≠ [] :=
begin
  /- don't know of a syntax like with -/
  apply in_not_nil 42,
  exact h,
end

/- learned about conv, still not able to apply at h -/
-- lemma in_not_nil_42_take3 (l : list ℕ) (h : In 42 l)
--   : l ≠ [] := sorry

lemma in_not_nil_42_take4 (l : list ℕ) (h : In 42 l)
  : l ≠ [] :=
begin
  apply @in_not_nil ℕ 42,
  exact h,
end

lemma in_not_nil_42_take5 (l : list ℕ) (h : In 42 l)
  : l ≠ [] :=
begin
  apply in_not_nil _ _ h,
end

/-
Example lemma_application_ex :
  ∀{n : nat} {ns : list nat},
    In n (map (fun m ⇒ m * 0) ns) →
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.
-/

/-
didn't spend a lot of time, but couldn't get lean
to compile this
-/

/-
Example function_equality_ex1 :
  (fun x ⇒ 3 + x) = (fun x ⇒ (pred 4) + x).
Proof. reflexivity. Qed.
-/

example : (λ x, 3 + x) = (λ x, (pred 4) + x) := rfl

/-
Example function_equality_ex2 :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
   (* Stuck *)
Abort.
-/

-- example : (λ x, x + 1) = (λ x, 1 + x) := sorry

/-
Axiom functional_extensionality : ∀{X Y: Type}
                                    {f g : X → Y},
  (∀(x:X), f x = g x) → f = g.
-/


axiom functional_extensionality
  {α β : Type} {f g : α → β}
  : (∀ a, f a = g a) → f = g

/-
Example function_equality_ex2 :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.
-/

lemma function_equality_ex₂ : (λ x, x + 1) = (λ x, 1 + x) :=
begin
  apply functional_extensionality,
  intro,
  rw add_comm,
end

/- built in as funext -/

example : (λ x, x + 1) = (λ x, 1 + x) :=
begin
  funext,
  rw add_comm,
end

/-
Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)
-/

#print axioms function_equality_ex₂

/-
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] ⇒ l2
  | x :: l1' ⇒ rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].
-/

open poly

def rev_append {α : Type} : lst α → lst α → lst α
| ⟦⟧ l₂ := l₂
| (h::t) l₂ := rev_append t (h::l₂)

def tr_rev {α : Type} (l : lst α) := rev_append l ⟦⟧

/-
Lemma tr_rev_correct : ∀X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
-/

/-
ih : tr_rev t = rev t
⊢ rev_append t ⟦h⟧ = rev t ++ ⟦h⟧
-/

/-
did a fair amount of hacking to have clean term language code generated
taking the list without funext is slightly nicer

also went for being pretty explicit

dsimp does less magic than unfold, 'unfold foo' is basically 'simp only [foo]'

the lemma and theorem can pretty much just be done with simp*
this is 4 stars because finding the lemma to define is non-trivial
-/

lemma rev_app {α : Type} (l₁ : lst α)
  : ∀ l₂ l₃, rev_append l₁ l₂ ++ l₃ = rev_append l₁ (l₂ ++ l₃) :=
begin
  induction l₁ with h₁ t₁ ih; intros,
    refl,
  dsimp only [rev_append],
  rw ih,
  refl,
end

lemma tr_rev_correct {α : Type} : @tr_rev α = @rev α :=
begin
  funext,
  induction l with h t ih; dsimp only [rev_append, tr_rev, rev],
    refl,
  rw ←ih,
  dsimp only [rev_append, tr_rev],
  rw rev_app,
  dsimp only [app],
  refl,
end

/-
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.
-/

example : evenb 42 = tt := rfl

/-
Example even_42_prop : ∃k, 42 = double k.
Proof. ∃21. reflexivity. Qed.
-/

example : ∃ (k : ℕ), 42 = double k
  := ⟨21, rfl⟩

/-
Theorem evenb_double : ∀k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.
-/

theorem evenb_double (k : ℕ)
  : evenb (double k) = tt :=
begin
  induction k with k ih,
    refl,
  simp,
  exact ih,
end

/-
Theorem evenb_double_conv : ∀n,
  ∃k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the evenb_S lemma from Induction.v. *)
  (* FILL IN HERE *) Admitted.
-/

-- doesn't work, but should be something like...
-- theorem evenb_double_conv :
--   ∀ n, ∃ k, n = if evenb n
--            then double k
--            else succ (double k)
-- | 0 := <0, rfl⟩
-- | 1 := ⟨1, rfl⟩
-- | (succ (succ n)) := ⟨succ evenb_double_conv n, rfl⟩

theorem evenb_double_conv (n : ℕ)
  : ∃ k, n = if evenb n
             then double k
             else succ (double k) :=
begin
  induction n with n ih,
    exact ⟨0, rfl⟩,
  cases h : (evenb n); cases ih with w ih; simp * at *,
    exact ⟨succ w, rfl⟩,
  exact ⟨w, rfl⟩
end

theorem even_bool_prop (n : ℕ)
  : evenb n = tt ↔ ∃ k, n = double k :=
begin
  split,
    intro h,
    cases (evenb_double_conv n) with k hk,
    rw hk,
    rw h,
    exact ⟨k, rfl⟩,
  intro k,
  cases k with k hk,
  rw hk,
  apply evenb_double,
end

/-
Theorem eqb_eq : ∀n1 n2 : nat,
  n1 =? n2 = true ↔ n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.
-/

open lists

theorem eqb_eq (n₁ n₂ : ℕ)
  : n₁ =? n₂ = tt ↔ n₁ = n₂ :=
begin
  split,
    apply eqb_true,
  intro h,
  rw h,
  rw ←eqb_refl,
end

/-
Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.
-/

/-
n = 2 is decidable, so lean allows it
not all props are
-/
def is_even_prime (n : ℕ) :=
  if n = 2 then tt else ff

/-
Example even_1000 : ∃k, 1000 = double k.
Proof. ∃500. reflexivity. Qed.
-/

example : ∃k, 1000 = double k := ⟨500, rfl⟩

/-
Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.
-/

example : evenb 1000 := rfl

/-
Example even_1000'' : ∃k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.
-/

/-
iffs are much less convenient to work
with in lean
-/
example : ∃k, 1000 = double k :=
begin
  apply (even_bool_prop _).mp,
  refl,
end

/-
Example not_even_1001 : evenb 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.
-/

example : evenb 1001 = ff := rfl

/-
Example not_even_1001' : ~(∃k, 1001 = double k).
Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.
-/

example : ¬(∃k, 1001 = double k) :=
begin
  rw ←even_bool_prop,
  simp
end

/-
Lemma plus_eqb_example : ∀n m p : nat,
    n =? m = true → n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.
-/

lemma plus_eqb_example (n m p : ℕ) (h : n =? m = tt)
  : n + p =? m + p = tt :=
begin
  rw eqb_eq at *,
  rw h,
end

/-
Lemma andb_true_iff : ∀b1 b2:bool,
  b1 && b2 = true ↔ b1 = true ∧ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : ∀b1 b2,
  b1 || b2 = true ↔ b1 = true ∨ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma andb_true_iff (b₁ b₂ : bool)
  : b₁ && b₂ = tt ↔ b₁ = tt ∧ b₂ = tt :=
by split; intro h; simp at *; exact h

lemma orb_true_iff (b₁ b₂ : bool)
  : b₁ || b₂ = tt ↔ b₁ = tt ∨ b₂ = tt :=
by split; intro h; simp at *; exact h

/-
Theorem eqb_neq : ∀x y : nat,
  x =? y = false ↔ x ≠ y.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- how is this one star? -/

theorem eqb_neq (x y : ℕ)
  : x =? y = ff ↔ x ≠ y :=
begin
  split; intro h,
    simp at *,
    by_contra c,
    rw c at h,
    simp at h,
    contradiction,
  simp at h,
  induction x with x ih generalizing y,
    cases y with y,
      contradiction,
    simp,
  cases y with y,
    simp,
  have : ¬x = y,
    by_contra c,
    have : succ x = succ y,
      exact congr_arg _ c,
    contradiction,
  simp,
  exact ih y this,
end

/-
Fixpoint eqb_list {A : Type} (eqb : A → A → bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma eqb_list_true_iff :
  ∀A (eqb : A → A → bool),
    (∀a1 a2, eqb a1 a2 = true ↔ a1 = a2) →
    ∀l1 l2, eqb_list eqb l1 l2 = true ↔ l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
-/

@[simp]
def eqb_list {α : Type} (eqb : α → α → bool)
  : list α → list α → bool
| [] [] := tt
| (h₁::t₁) (h₂::t₂) := eqb h₁ h₂ && eqb_list t₁ t₂
| _ _ := ff

lemma eqb_list_true_iff {α : Type}
  (eqb : α → α → bool)
  (heq : ∀ a₁ a₂, eqb a₁ a₂ = tt ↔ a₁ = a₂)
  (l₁ : list α)
  (l₂ : list α)
  : eqb_list eqb l₁ l₂ ↔ l₁ = l₂ :=
begin
  split;
    intro h;
    induction l₁ with h₁ t₁ ih generalizing l₂;
      cases l₂ with h₂ t₂;
        simp;
        simp at h;
        try { contradiction },
    exact ⟨(heq _ _).mp h.left, ih _ h.right⟩,
  exact ⟨(heq _ _).mpr h.left, ih _ h.right⟩
end

/-
Theorem forallb_true_iff : ∀X test (l : list X),
   forallb test l = true ↔ All (fun x ⇒ test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem forallb_true_iff {α : Type} (p : α → bool) (l : list α)
  : forallb p l = tt ↔ all (λ a, p a = tt) l :=
begin
  split;
    intro h;
    induction l with _ _ ih;
      simp at *;
      contradiction <|> exact ⟨h.left, ih h.right⟩,
end

/-
Definition excluded_middle := ∀P : Prop,
  P ∨ ¬P.
-/

def excluded_middle := ∀ p, p ∨ ¬p

/-
Theorem restricted_excluded_middle : ∀P b,
  (P ↔ b = true) → P ∨ ¬P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.
-/

theorem restricted_excluded_middle (p : Prop) (b : bool) (h : p ↔ b = tt)
  : p ∨ ¬p := by cases b; simp * at *

/-
Theorem restricted_excluded_middle_eq : ∀(n m : nat),
  n = m ∨ n ≠ m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.
-/

theorem restricted_excluded_middle_eq (n m : ℕ) : n = m ∨ n ≠ m :=
begin
  apply restricted_excluded_middle (n = m) (n =? m),
  symmetry,
  apply eqb_eq,
end

/-
Theorem excluded_middle_irrefutable: ∀(P:Prop),
  ¬¬(P ∨ ¬P).
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
not sure if this technique has been used before in the book
-/

theorem excluded_middle_irrefutable (p : Prop) : ¬¬(p ∨ ¬p) :=
begin
  by_contradiction h,
  have hnp : ¬p,
    by_contradiction hp,
    have c : p ∨ ¬p,
      exact or.inl hp,
    contradiction,
  have c : p ∨ ¬p,
    exact or.inr hnp,
  contradiction,
end

/-
Theorem not_exists_dist :
  excluded_middle →
  ∀(X:Type) (P : X → Prop),
    ¬(∃x, ¬P x) → (∀x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem not_exists_dist {α : Type}
  (em : excluded_middle) (p : α → Prop) (h : ¬(∃a, ¬p a)) : ∀a, p a :=
begin
  intro a,
  cases (em (p a)) with hp hnp,
    exact hp,
  have c : ∃a, ¬p a,
    exact ⟨a, hnp⟩,
  contradiction,
end

/-
Definition peirce := ∀P Q: Prop,
  ((P→Q)→P)→P.

Definition double_negation_elimination := ∀P:Prop,
  ~~P → P.

Definition de_morgan_not_and_not := ∀P Q:Prop,
  ~(~P ∧ ¬Q) → P∨Q.

Definition implies_to_or := ∀P Q:Prop,
  (P→Q) → (¬P∨Q).
-/

/-
TODO - peirce
-/

/- peirce and peirce' are in core -/
def peirce'' (p q : Prop) (h : (p → q) → p) := p

def double_negation_elimination (p : Prop) (h : ¬¬p) := p

def de_morgan_not_and_not (p q : Prop) (h : ¬(¬p ∧ ¬q)) := p ∨ q

def implies_to_or (p q : Prop) (h : p → q) := ¬p ∨ q

