import tactic.basic
import .ch05_tactics

open basics (oddb evenb eqb)
open induction (double evenb_succ)
open lists (eqb_refl)
open tactics (eqb_true)

open list (map cons_append nil_append)
open nat (pred succ eq_zero_of_mul_eq_zero)

namespace logic

variables {α β γ : Type}
variable {a : α}
variables {P Q R : Prop}
variables {m n o p : ℕ}
variables {l l' : list α}

/-
Check 3 = 3.
(* ===> Prop *)
Check ∀n m : nat, n + m = m + n.
(* ===> Prop *)
-/

#check 3 = 3

#check ∀n m : ℕ, n + m = m + n

/-
Check 2 = 2.
(* ===> Prop *)
Check ∀n : nat, n = 2.
(* ===> Prop *)
Check 3 = 4.
(* ===> Prop *)
-/

#check 2 = 2

#check ∀n : ℕ, n = 2

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

def plus_fact : Prop := 2 + 2 = 4

#check plus_fact

/-
Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.
-/

theorem plus_fact_is_true : plus_fact := by rw plus_fact

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

def injective (f : α → β) :=  ∀(x y: α), f x = f y → x = y

lemma nat.succ_inj : injective succ :=
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

example : 3 + 4 = 7 ∧ 2 * 2 = 4 :=
begin
  split,
    refl,
  refl,
end

/-
Lemma and_intro : ∀A B : Prop, A → B → A ∧ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.
-/

/- TODO: be better about namespacing earlier defs -/
lemma and.intro (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

/-
Example and_example' : 3 + 4 = 7 ∧ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.
-/

example : 3 + 4 = 7 ∧ 2 * 2 = 4 :=
begin
  apply and.intro,
    refl,
  refl,
end

/-
Example and_exercise :
  ∀n m : nat, n + m = 0 → n = 0 ∧ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- can't be example as it's used below -/
lemma and_exercise : ∀(n m : ℕ) (h : n + m = 0), n = 0 ∧ m = 0
| 0 0 h :=
begin
  split,
    refl,
  refl,
end
| (n + 1) m h :=
begin
  rw [add_comm, ←add_assoc] at h,
  cases h,
end
| n (m + 1) h :=
begin
  rw [←add_assoc] at h,
  cases h,
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

lemma and_example₂ (h : n = 0 ∧ m = 0) : n + m = 0 :=
begin
  cases h with hn hm,
  rw [hn, hm],
end

/-
Lemma and_example2' :
  ∀n m : nat, n = 0 ∧ m = 0 → n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
-/

lemma and_example₂' : n = 0 ∧ m = 0 → n + m = 0 :=
begin
  rintro ⟨hn, hm⟩,
  rw [hn, hm],
end

/-
Lemma and_example2'' :
  ∀n m : nat, n = 0 → m = 0 → n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
-/

lemma and_example2'' (hn : n = 0) (hm : m = 0) : n + m = 0 := by rw [hn, hm]

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

lemma and_example₃ (h : n + m = 0) : n * m = 0 :=
begin
  have h : n = 0 ∧ m = 0,
    apply and_exercise,
    exact h,
  cases h with hn hm,
  rw hn,
  rw zero_mul,
end

/-
Lemma proj1 : ∀P Q : Prop,
  P ∧ Q → P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.
-/

lemma and.left (h : P ∧ Q) : P :=
begin
  cases h with hp hq,
  apply hp,
end

/- h.1 also works -/
lemma and.left' (h : P ∧ Q) : P := h.left

/-
Lemma proj2 : ∀P Q : Prop,
  P ∧ Q → Q.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma and.right (h : P ∧ Q) : Q := h.right

/-
Theorem and_commut : ∀P Q : Prop,
  P ∧ Q → Q ∧ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.
-/

theorem and.comm (h : P ∧ Q) : Q ∧ P := ⟨h.right, h.left⟩

/-
Theorem and_assoc : ∀P Q R : Prop,
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* FILL IN HERE *) Admitted.
-/

theorem and.assoc (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) :=
  ⟨h.left.left, h.left.right, h.right⟩

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

lemma or_example (h : n = 0 ∨ m = 0) : n * m = 0 :=
begin
  cases h with hn hm,
    rw hn,
    rw zero_mul,
  rw hm,
  refl,
end

/-
Lemma or_intro : ∀A B : Prop, A → A ∨ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.
-/

lemma or.inl (p : P) : P ∨ Q :=
begin
  left,
  exact p,
end

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

lemma nat.eq_zero_or_eq_succ_pred : n = 0 ∨ n = succ (pred n) :=
begin
  cases n,
    exact or.inl rfl,
  exact or.inr rfl,
end

/-
Module MyNot.

Definition not (P:Prop) := P → False.

Notation "¬x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.
-/

def not (P : Prop) := P → false

local prefix `¬` := not

#check not

/-
Theorem ex_falso_quodlibet : ∀(P:Prop),
  False → P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.
-/

theorem false.rec (f : false) : P := by cases f

/-
Fact not_implies_our_not : ∀(P:Prop),
  ¬P → (∀(Q:Prop), P → Q).
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma absurd (hnp : ¬P) (hp : P) : Q := false.rec (hnp hp)

/-
Notation "x ≠ y" := (~(x = y)).
-/

local notation x ≠ y := ¬(x = y)

/-
Theorem zero_not_one : 0 ≠ 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.
-/

theorem zero_ne_one : 0 ≠ 1 :=
begin
  unfold not,
  rintro ⟨contra⟩,
end

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

theorem not_false : ¬false :=
begin
  unfold not,
  rintro ⟨h⟩,
end

theorem contradiction_implies_anything (h : P ∧ ¬P) : Q :=
begin
  cases h with hp hnp,
  unfold not at hnp,
  replace hp, exact hnp hp,
  cases hp,
end

theorem non_contradictory_intro (h : P) : ¬¬P :=
begin
  unfold not,
  intro g,
  apply g,
  exact h,
end

/-
Theorem contrapositive : ∀(P Q : Prop),
  (P → Q) → (¬Q → ¬P).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem contrapositive (h: P → Q) : (¬Q → ¬P) :=
begin
  intro hnq,
  unfold not,
  intro p,
  exact absurd hnq (h p),
end

/-
Theorem not_both_true_and_false : ∀P : Prop,
  ¬(P ∧ ¬P).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem not_both_true_and_false : ¬(P ∧ ¬P) :=
begin
  unfold not,
  rintro ⟨hp, hnp⟩,
  exact hnp hp,
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

theorem not_true_is_false {b: bool} (h : b ≠ tt) : b = ff :=
begin
  cases b,
    refl,
  unfold not at h,
  apply false.rec,
  apply h,
  refl,
end

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

theorem not_true_is_false' {b : bool} (h : b ≠ tt) : b = ff :=
begin
  cases b,
    refl,
  unfold not at h,
  exfalso,
  apply h,
  refl,
end

/-
Lemma True_is_true : True.
Proof. apply I. Qed.
-/

lemma true_is_tt : true := trivial

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

section my_iff

/- this def doesn't work with rewrite -/
structure iff (P Q : Prop): Prop :=
intro :: (mp : P → Q) (mpr : Q → P)

local infix ↔ := iff

end my_iff

theorem iff.sym (h : P ↔ Q) : Q ↔ P :=
begin
  cases h with hpq hqp,
  split,
    exact hqp,
  exact hpq,
end

lemma not_true_iff_false (b: bool) : b ≠ tt ↔ b = ff :=
begin
  split,
    apply not_true_is_false,
  intro h,
  rw h,
  intro h',
  cases h',
end

/-
Theorem or_distributes_over_and : ∀P Q R : Prop,
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem or_and_distrib_left : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
begin
  split,
    rintro (hp | hqr),
      split,
        exact or.inl hp,
      exact or.inl hp,
    split,
      exact or.inr hqr.left,
    exact or.inr hqr.right,
  rintro ⟨hpq, hpr⟩,
  cases hpq with hp hq,
    exact or.inl hp,
  cases hpr with hp hr,
    exact or.inl hp,
  exact or.inr ⟨hq, hr⟩
end

/-
From Coq Require Import Setoids.Setoid.
-/

/-
nothing like that needed in lean
-/

/-
Lemma mult_0 : ∀n m, n * m = 0 ↔ n = 0 ∨ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  ∀P Q R : Prop, P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.
-/

lemma mul_zero : n * m = 0 ↔ n = 0 ∨ m = 0 :=
begin
  split,
   exact eq_zero_of_mul_eq_zero,
  apply or_example,
end

lemma or.assoc : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R :=
begin
  split,
    rintro (h | h | h),
        exact or.inl (or.inl h),
      exact or.inl (or.inr h),
    exact or.inr h,
  rintro (⟨h | h⟩ | h),
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

lemma mul_zero_three : n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 :=
begin
  rw [mul_zero, mul_zero],
  rewrite or.assoc,
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

lemma apply_iff_example (h : n * m = 0) : n = 0 ∨ m = 0 :=
begin
  apply mul_zero.mp,
  exact h,
end

/-
Lemma four_is_even : ∃n : nat, 4 = n + n.
Proof.
  ∃2. reflexivity.
Qed.
-/

lemma four_is_even : ∃n : ℕ, 4 = n + n := by use 2

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

theorem exists_example₂ (h : ∃m, n = 4 + m) : ∃o, n = 2 + o :=
begin
  cases h with m hm,
  use 2 + m,
  rw ←add_assoc,
  exact hm,
end

/-
Theorem dist_not_exists : ∀(X:Type) (P : X → Prop),
  (∀x, P x) → ¬(∃x, ¬P x).
Proof.
  (* FILL IN HERE *) Admitted.
-/

#check exists_or_distrib

theorem not_exists_not.mpr (p : α → Prop) (h : ∀x, p x) : ¬(∃x, ¬p x) :=
begin
  rintro ⟨a, hnp⟩,
  exact hnp (h a),
end

/-
Theorem dist_exists_or : ∀(X:Type) (P Q : X → Prop),
  (∃x, P x ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
-/

theorem exists_or_distrib (p q : α → Prop) :
  (∃a, p a ∨ q a) ↔ (∃a, p a) ∨ (∃a, q a) :=
begin
  split,
    rintro ⟨a, hp | hq⟩,
      exact or.inl ⟨a, hp⟩,
    exact or.inr ⟨a, hq⟩,
  rintro (⟨a, hp⟩ | ⟨a, hq⟩),
    exact ⟨a, or.inl hp⟩,
  exact ⟨a, or.inr hq⟩,
end

/-
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] ⇒ False
  | x' :: l' ⇒ x' = x ∨ In x l'
  end.
-/

def In (a : α) : list α → Prop
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

example : In 4 [1, 2, 3, 4, 5] :=
begin
  right,
  right,
  right,
  left,
  refl,
end

/-
oh yeah, rcases doing subst for rfl is awesome
-/
example (h : In n [2, 4]) : ∃n', n = 2 * n' :=
begin
  rcases h with rfl | rfl | ⟨⟨⟩⟩,
    use 1,
    refl,
  use 2,
  refl,
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

lemma in_map (f : α → β) (h : In a l) : In (f a) (l.map f) :=
begin
  induction l with a' l ih,
    cases h,
  rcases h with rfl | h,
    exact or.inl rfl,
  exact or.inr (ih h),
end

/-
Lemma In_map_iff :
  ∀(A B : Type) (f : A → B) (l : list A) (y : B),
    In y (map f l) ↔
    ∃x, f x = y ∧ In x l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
TODO: at this point, i realize a lot of unfold and rw aren't needed
      as unification will handle refl stuff
-/

lemma in_map_iff (f : α → β) (b : β) : In b (l.map f) ↔ ∃a, f a = b ∧ In a l :=
begin
  split,
    induction l with a l ih,
      rintro ⟨⟩,
    rintro (rfl | h),
      use a,
      split,
        refl,
      exact or.inl rfl,
    specialize ih h,
    rcases ih with ⟨a', rfl, ih⟩,
    use a',
    split,
      refl,
    exact or.inr ih,
  rintro ⟨a', rfl, h⟩,
  induction l with a l ih,
    cases h,
  rcases h with rfl | h,
    exact or.inl rfl,
  exact or.inr (ih h),
end

/-
Lemma In_app_iff : ∀A l l' (a:A),
  In a (l++l') ↔ In a l ∨ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma in_app_iff : In a (l ++ l') ↔ In a l ∨ In a l' :=
begin
  split,
    intro h,
    induction l with a' l ih,
      exact or.inr h,
    rcases h with rfl | h,
      exact or.inl (or.inl rfl),
    specialize ih h,
    cases ih,
      exact or.inl (or.inr ih),
    exact or.inr ih,
  rintro (h | h),
    induction l with a' l ih,
      cases h,
    rcases h with rfl | h,
      exact or.inl rfl,
    exact or.inr (ih h),
  cases l' with a' l',
    cases h,
  cases h,
    induction l with a'' l ih,
      exact or.inl h,
    exact or.inr ih,
  induction l with a'' l ih,
    exact or.inr h,
  exact or.inr ih,
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

def all (p : α → Prop) : list α → Prop
| [] := true
| (h::t) := p h ∧ all t

lemma all_in (p : α → Prop) : (∀{a}, In a l → p a) ↔ all p l :=
begin
  split,
    intro h,
    induction l with a l ih,
      unfold all,
    split,
      apply h,
      exact or.inl rfl,
    apply ih,
    intros a' i,
    exact h (or.inr i),
  induction l with a l ih,
    rintro h a' ⟨⟩,
  rintro ⟨hl, hr⟩ a' (rfl | i),
    exact hl,
  exact ih hr i,
end

/-
Definition combine_odd_even (Podd Peven : nat → Prop) : nat → Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

/-
either i super missed the mark with this def
or this is not a three star problem
-/

def combine_odd_even (podd peven : ℕ → Prop) (n : ℕ): Prop :=
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
  (podd peven : ℕ → Prop)
  (hodd : oddb n = true → podd n)
  (heven : oddb n = false → peven n)
  : combine_odd_even podd peven n :=
begin
  unfold combine_odd_even,
  cases oddb n,
    exact heven rfl,
  exact hodd rfl,
end

theorem combine_odd_even_elim_odd
  (podd peven : ℕ → Prop)
  (h : combine_odd_even podd peven n)
  (hodd : oddb n = true)
  : podd n :=
begin
  unfold combine_odd_even at h,
  cases oddb n,
    cases hodd,
  exact h,
end

theorem combine_odd_even_elim_even
  (podd peven : ℕ → Prop)
  (h : combine_odd_even podd peven n)
  (heven : oddb n = false)
  : peven n :=
begin
  unfold combine_odd_even at h,
  cases oddb n,
    exact h,
  cases heven,
end

/-
Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)
-/

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

-- lemma plus_comm3 : n + (m + o) = (o + m) + m :=
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

lemma plus_comm3_take2 : n + (m + o) = (o + m) + n :=
begin
  rw add_comm,
  have h : m + o = o + m, rw add_comm,
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

/-
TODO: i find it unlikely i haven't used this earlier
-/
lemma plus_comm3_take3 : n + (m + o) = (o + m) + n :=
begin
  rw add_comm,
  /- i assume partial app works in coq as well -/
  rw add_comm m,
end

/-
Lemma in_not_nil :
  ∀A (x : A) (l : list A), In x l → l ≠ [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.
-/

lemma in_not_nil (h : In a l) : l ≠ [] :=
begin
  unfold not,
  intro hl,
  cases l with a l,
    cases h,
  cases hl,
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

/- this works perfectly fine in lean -/
lemma in_not_nil_42 (l : list ℕ) (h : In 42 l) : l ≠ [] :=
begin
  apply in_not_nil,
  exact h,
end

/-
TODO: see if lean has named parameters
-/
lemma in_not_nil_42_take2 (l : list ℕ) (h : In 42 l) : l ≠ [] :=
begin
  /- don't know of a syntax like with -/
  apply in_not_nil,
  exact h,
end

/- learned about conv, still not able to apply at h -/
-- lemma in_not_nil_42_take3 (l : list ℕ) (h : In 42 l)
--   : l ≠ [] := sorry

lemma in_not_nil_42_take4 (l : list ℕ) (h : In 42 l) : l ≠ [] :=
begin
  apply @in_not_nil ℕ 42,
  exact h,
end

lemma in_not_nil_42_take5 (l : list ℕ) (h : In 42 l) : l ≠ [] :=
by apply in_not_nil h

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

example {ns: list ℕ} (h : In n (ns.map (λm, m * 0))): n = 0 :=
begin
  cases (in_map_iff _ _).mp h with m hm,
  rw ←hm.left,
  refl,
end

/-
Example function_equality_ex1 :
  (fun x ⇒ 3 + x) = (fun x ⇒ (pred 4) + x).
Proof. reflexivity. Qed.
-/

example : (λx, 3 + x) = (λx, (pred 4) + x) := rfl

/-
Example function_equality_ex2 :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
   (* Stuck *)
Abort.
-/

-- example : (λx, x + 1) = (λx, 1 + x) := sorry

/-
Axiom functional_extensionality : ∀{X Y: Type}
                                    {f g : X → Y},
  (∀(x:X), f x = g x) → f = g.
-/


axiom functional_extensionality {f g : α → β} : (∀a, f a = g a) → f = g

/-
Example function_equality_ex2 :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.
-/

lemma function_equality_ex₂ : (λx, x + 1) = (λx, 1 + x) :=
begin
  apply functional_extensionality,
  intro x,
  rw add_comm,
end

/- built in as funext -/
/-
TODO: examine previous definitions that have tactics
-/

example : (λx, x + 1) = (λx, 1 + x) :=
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

section reverse

/- using poly.list as the library uses a rev_append style reverse -/

open poly.list

local notation `[]` := nil
local infix :: := cons
local infix ++ := append

def rev_append : poly.list α → poly.list α → poly.list α
| [] l₂ := l₂
| (h::t) l₂ := rev_append t (h::l₂)

def tr_rev (l: poly.list α) := rev_append l []

/-
Lemma tr_rev_correct : ∀X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
-/

lemma rev_app (l₁ l₂ l₃: poly.list α)
  : rev_append l₁ l₂ ++ l₃ = rev_append l₁ (l₂ ++ l₃) :=
begin
  induction l₁ with a l₁ ih generalizing l₂ l₃,
    refl,
  unfold rev_append,
  rw ih,
  refl,
end

lemma tr_rev_correct : @tr_rev α = reverse :=
begin
  funext,
  induction l with a l ih,
    refl,
  unfold reverse,
  rw ←ih,
  unfold rev_append tr_rev,
  rw rev_app,
  refl,
end

end reverse

/-
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.
-/

example : evenb 42 = tt := rfl

/-
Example even_42_prop : ∃k, 42 = double k.
Proof. ∃21. reflexivity. Qed.
-/

example : ∃k, 42 = double k := ⟨21, rfl⟩

/-
Theorem evenb_double : ∀k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.
-/

theorem evenb_double (k) : evenb (double k) = tt :=
begin
  induction k with k ih,
    refl,
  unfold double evenb,
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

theorem evenb_double_conv
  : ∃k, n = if evenb n then double k else succ (double k) :=
begin
  induction n with n ih,
    exact ⟨0, rfl⟩,
  cases ih with k ih,
    rw evenb_succ,
    conv in (n + 1) { rw ih, },
    cases h : evenb n,
      use succ k,
      refl,
    use k,
    refl,
end

theorem evenb_double_conv'
  : ∀n, ∃k, n = if evenb n then double k else succ (double k)
| 0 := ⟨0, rfl⟩
| 1 := ⟨0, rfl⟩
| (n + 2) :=
begin
  cases evenb_double_conv' n with k ih,
  use succ k,
  rw [evenb_succ, evenb_succ],
  conv in (n + 2) { rw ih, },
  cases evenb n,
    refl,
  refl,
end

/-
Theorem even_bool_prop : ∀n,
  evenb n = true ↔ ∃k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. ∃k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.
-/

theorem even_bool_prop : evenb n = tt ↔ ∃k, n = double k :=
begin
  split,
    intro h,
    cases (@evenb_double_conv n) with k hk,
    rw hk,
    rw h,
    exact ⟨k, rfl⟩,
  rintro ⟨k, rfl⟩,
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

theorem eqb_eq : n =? m = tt ↔ n = m :=
begin
  split,
    apply eqb_true,
  rintro rfl,
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
def is_even_prime := if n = 2 then tt else ff

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
need to mention the direction in lean
-/
example : ∃k, 1000 = double k :=
begin
  apply even_bool_prop.mp,
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
  unfold not,
  intro h,
  cases h,
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

lemma plus_eqb_example (h : n =? m = tt) : n + p =? m + p = tt :=
begin
  rw eqb_eq at h ⊢,
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

lemma band_eq_true_eq_eq_tt_and_eq_tt (b₁ b₂ : bool)
  : b₁ && b₂ = tt ↔ b₁ = tt ∧ b₂ = tt :=
begin
  split,
    intro h,
    cases b₁,
      cases h,
    cases b₂,
      cases h,
    exact ⟨rfl, rfl⟩,
  rintro ⟨rfl, rfl⟩,
  refl,
end

lemma bor_eq_true_eq_eq_tt_or_eq_tt (b₁ b₂ : bool)
  : b₁ || b₂ = tt ↔ b₁ = tt ∨ b₂ = tt :=
begin
  split,
    intro h,
    cases b₁,
      cases b₂,
        cases h,
      exact or.inr rfl,
    exact or.inl rfl,
  rintro (rfl | rfl),
    refl,
  cases b₁,
    refl,
  refl,
end

/-
Theorem eqb_neq : ∀x y : nat,
  x =? y = false ↔ x ≠ y.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- how is this one star? -/
theorem eqb_neq : n =? m = ff ↔ n ≠ m :=
begin
  split,
    intro h,
    rintro rfl,
    rw eqb_refl n at h,
    cases h,
  intro c,
  unfold not at c,
  induction n with n ih generalizing m,
    cases m,
      cases c rfl,
    refl,
  cases m,
    refl,
  unfold eqb,
  apply ih,
  rintro rfl,
  exact c rfl,
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

def eqb_list (eqb : α → α → bool) : list α → list α → bool
| [] [] := tt
| (h₁::t₁) (h₂::t₂) := eqb h₁ h₂ && eqb_list t₁ t₂
| _ _ := ff

lemma eqb_list_true_iff
  (eqb : α → α → bool)
  (heq : ∀a₁ a₂, eqb a₁ a₂ = tt ↔ a₁ = a₂)
  (l₁ : list α)
  (l₂ : list α)
  : eqb_list eqb l₁ l₂ = tt ↔ l₁ = l₂ :=
begin
  split,
    intro h,
    induction l₁ with h₁ t₁ ih generalizing l₂,
      cases l₂ with h₂ t₂,
        refl,
      cases h,
    cases l₂ with h₂ t₂,
      cases h,
    unfold eqb_list at h,
    rw band_eq_true_eq_eq_tt_and_eq_tt at h,
    congr,
      rw heq at h,
      exact h.left,
    exact ih _ h.right,
  rintro rfl,
  induction l₁ with h₁ t₁ ih,
    refl,
  unfold eqb_list,
  rw ih,
  rw (heq h₁ h₁).mpr rfl,
  refl,
end

/-
Theorem forallb_true_iff : ∀X test (l : list X),
   forallb test l = true ↔ All (fun x ⇒ test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem all_true_iff (p : α → bool) : l.all p = tt ↔ all (λa, p a = tt) l :=
begin
  split,
    intro h,
    induction l with a l ih,
      unfold all,
    unfold all,
    unfold list.all list.foldr at h,
    rw band_eq_true_eq_eq_tt_and_eq_tt at h,
    exact ⟨h.left, ih h.right⟩,
  intro h,
  induction l with a l ih,
    refl,
  unfold all at h,
  unfold list.all list.foldr,
  rw band_eq_true_eq_eq_tt_and_eq_tt,
  exact ⟨h.left, ih h.right⟩,
end

/-
Definition excluded_middle := ∀P : Prop,
  P ∨ ¬P.
-/

def classical.em := ∀P : Prop, P ∨ ¬P

/-
Theorem restricted_excluded_middle : ∀P b,
  (P ↔ b = true) → P ∨ ¬P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.
-/

theorem restricted_excluded_middle (b : bool) (h : P ↔ b = tt) : P ∨ ¬P :=
begin
  rw h,
  cases b,
    right,
    rintro ⟨⟩,
  exact or.inl rfl,
end

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

theorem restricted_excluded_middle_eq : n = m ∨ n ≠ m :=
begin
  apply @restricted_excluded_middle (n = m) (n =? m),
  symmetry,
  exact eqb_eq,
end

/-
Theorem excluded_middle_irrefutable: ∀(P:Prop),
  ¬¬(P ∨ ¬P).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem excluded_middle_irrefutable (P : Prop) : ¬¬(P ∨ ¬P) :=
begin
  intro h,
  apply h,
  right,
  intro p,
  apply h,
  exact or.inl p,
end

/-
Theorem not_exists_dist :
  excluded_middle →
  ∀(X:Type) (P : X → Prop),
    ¬(∃x, ¬P x) → (∀x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem not_exists_dist (em : classical.em) (p : α → Prop) (h : ¬(∃a, ¬p a))
  : p a :=
begin
  cases em (p a) with hp hnp,
    exact hp,
  have c : ∃a, ¬p a,
    exact ⟨a, hnp⟩,
  exact absurd h c,
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

/- peirce and peirce' are in core -/
def peirce := ∀P Q : Prop, ((P → Q) → P) → P

def double_negation_elimination := ∀P : Prop, ¬¬P → P

def de_morgan_not_and_not := ∀P Q : Prop, ¬(¬P ∧ ¬Q) → P ∨ Q

def implies_to_or := ∀P Q : Prop, (P → Q) → ¬P ∨ Q

def em_iff_peirce : classical.em ↔ peirce :=
begin
  unfold classical.em peirce,
  split,
    intros em P Q h,
    cases em P with p np,
      exact p,
    apply h,
    intro p,
    exact absurd np p,
  intros peirce P,
  apply peirce _ false,
  intro h,
  right,
  intro p,
  exact h (or.inl p),
end

def em_iff_dne : classical.em ↔ double_negation_elimination :=
begin
  unfold classical.em double_negation_elimination,
  split,
    intros em P nnp,
    cases em P with p np,
      exact p,
    exact absurd nnp np,
  intros dne P,
  exact dne _ (excluded_middle_irrefutable P),
end

def em_iff_dmnn : classical.em ↔ de_morgan_not_and_not :=
begin
  unfold classical.em de_morgan_not_and_not,
  split,
    intros em P Q npq,
    cases em P with p np,
      exact or.inl p,
    cases em Q with q nq,
      exact or.inr q,
    exact absurd npq ⟨np, nq⟩,
  intros dmnn P,
  apply dmnn,
  rintro ⟨np, nnp⟩,
  exact absurd nnp np,
end

def em_iff_tor : classical.em ↔ implies_to_or :=
begin
  unfold classical.em implies_to_or,
  split,
    intros em P Q hpq,
    cases em P with p np,
      exact or.inr (hpq p),
    exact or.inl np,
  intros tor P,
  rw or.comm,
  apply tor,
  exact id,
end

end logic