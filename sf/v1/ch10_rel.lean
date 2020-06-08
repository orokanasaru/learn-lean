import tactic.basic
import .ch07_indprop

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

/- a bit different -/
#print has_le.le

#check (has_le.le : ℕ → ℕ → Prop)
#check (has_le.le : relation ℕ)

/-
Definition partial_function {X: Type} (R: relation X) :=
  ∀x y1 y2 : X, R x y1 → R x y2 → y1 = y2.
-/

def partial_function {α} (R : relation α) :=
  ∀ {x y₁ y₂} (h₁ : R x y₁) (h₂ : R x y₂), y₁ = y₂

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

open nat

theorem le_not_a_partial_function : ¬partial_function less_than_or_equal :=
begin
  by_contradiction c,
  unfold partial_function at c,
  have : 0 = 1,
    apply @c 0 0 1,
      apply less_than_or_equal.refl,
    apply less_than_or_equal.step,
    apply less_than_or_equal.refl,
  contradiction,
end

theorem total_relation_not_partial : ¬partial_function total_relation :=
begin
  by_contradiction c,
  unfold partial_function at c,
  have, exact c (total_relation.intro 0 0) (total_relation.intro 0 1),
  contradiction,
end

theorem empty_relation_partial : partial_function empty_relation' :=
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

def reflexive' {α} (R : relation α) :=
  ∀a, R a a

open le

theorem le_reflexive : reflexive le :=
begin
  unfold reflexive,
  intro,
  apply le_n,
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

def transitive' {α} (R : relation α) :=
  ∀ {a b c : α} (hab : R a b) (hbc : R b c), R a c

theorem le_trans'' : transitive' le :=
begin
  unfold transitive',
  intros,
  induction hbc,
  case le_n { exact hab, },
  case le_s : n m h ih {
    apply le_s,
    exact ih hab,
  },
end

theorem lt_trans' : transitive' lt :=
begin
  unfold transitive' lt,
  intros,
  exact le_trans'' (le_s hab) hbc,
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

theorem lt_trans''' : transitive' lt :=
begin
  unfold transitive' lt,
  intros,
  generalize heq : succ b = b',
  rw heq at hbc,
  induction hbc,
  case le_n {
    rw ←heq,
    exact le_s hab,
  },
  case le_s : b' c' h ih {
    exact le_s (ih heq),
  },
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

theorem lt_trans'''' : transitive' lt :=
begin
  unfold transitive' lt,
  intros,
  induction c with c' ih,
    cases hbc,
  cases hbc with _ _ _ h,
    exact le_s hab,
  exact le_s (ih h),
end

/-
Theorem le_Sn_le : ∀n m, S n ≤ m → n ≤ m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.
-/

theorem le_Sn_le {n m} (h : succ n ≤' m) : n ≤' m :=
begin
  apply le_trans'',
    exact le_s (le_n n),
  exact h,
end

/-
Theorem le_S_n : ∀n m,
  (S n ≤ S m) → (n ≤ m).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem le_S_n {n m} (h : succ n ≤' succ m) : n ≤' m :=
begin
  cases h with _ _ _ h,
    apply le_n,
  exact le_Sn_le h,
end

/-
Theorem le_Sn_n : ∀n,
  ¬(S n ≤ n).
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- induction c leads to fun -/

theorem le_Sn_n (n) : ¬(succ n ≤' n) :=
begin
  by_contra c,
  induction n with n' ih,
    cases c,
  exact ih (le_S_n c),
end

/-
Definition symmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) → (R b a).
-/

def symmetric' {α} (R : relation α) :=
  ∀ {a b : α} (h : R a b), R b a

/-
Theorem le_not_symmetric :
  ¬(symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem le_not_symmetric : ¬symmetric' le :=
begin
  unfold symmetric',
  by_contra c,
  cases c (le_s (le_n 0)),
end

/-
Definition antisymmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) → (R b a) → a = b.
-/

def antisymmetric {α} (R : relation α) :=
  ∀ {a b} (hab : R a b) (hba : R b a), a = b

/-
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem le_antisymmetric : antisymmetric le :=
begin
  unfold antisymmetric,
  intros,
  induction a with a' ih generalizing b,
    cases hba,
    refl,
  cases b,
    cases hab,
  exact congr_arg _ (ih (le_S_n hab) (le_S_n hba)),
end

/-
Theorem le_step : ∀n m p,
  n < m →
  m ≤ S p →
  n ≤ p.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
a lot of false starts
look at the definition of <
-/

theorem le_step {n m p}
  (hn : n <' m) (hm : m ≤' succ p) : n ≤' p :=
  le_S_n $ le_trans'' hn hm

-- theorem z_le (n) : 0 ≤' n :=
-- begin
--   induction n with n ih,
--     exact le_n 0,
--   exact le_s ih,
-- end

-- theorem le_step {n m p}
--   (hn : n <' m) (hm : m ≤' succ p) : n ≤' p :=
-- begin
--   induction m with m' ih generalizing n p,
--     cases hn,
--   cases n,
--     exact z_le p,
--   cases p,
--     cases hm,
--       cases hn,
--       cases hn_h,
--     cases hm_h,
--   cases hn,
--     exact le_S_n hm,
--   exact ih (hn_h) (le_Sn_le hm),
-- end

/-
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) ∧ (symmetric R) ∧ (transitive R).
-/

def equivalence' {α} (R : relation α) :=
  reflexive' R ∧ symmetric' R ∧ transitive' R

/-
Definition order {X:Type} (R: relation X) :=
  (reflexive R) ∧ (antisymmetric R) ∧ (transitive R).
-/

def order {α} (R : relation α) :=
  reflexive' R ∧ antisymmetric R ∧ transitive' R

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

def preorder' {α} (R : relation α) :=
  reflexive' R ∧ transitive' R

/- not sure why exact doesn't work -/

theorem le_order : order le :=
begin
  unfold order,
  split,
    apply le_reflexive,
  split,
    apply le_antisymmetric,
  apply le_trans'',
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

inductive clos_refl_trans {α} (R : relation α) : relation α
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

open next_nat

theorem next_nat_closure_is_le (n m)
  : n ≤' m ↔ (clos_refl_trans next_nat) n m :=
begin
  split,
    intro h,
    induction h,
    case le_n { apply rt_refl, },
    case le_s : n' m' h' ih {
      exact rt_trans ih (rt_step (nn _)),
    },
  intro h,
  induction h,
  case rt_step : n' m' h {
    cases h,
    exact le_s (le_n _),
  },
  case rt_refl { apply le_n, },
  case rt_trans : x y z hxy hyz ihx ihy {
    exact le_trans'' ihx ihy,
  },
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

inductive clos_refl_trans_1n {α} (R : relation α) : α → α → Prop
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

lemma rsc_R {α} {R : relation α} {x y} (h : R x y)
  : clos_refl_trans_1n R x y := rt1n_trans h (rt1n_refl y)

/-
Lemma rsc_trans :
  ∀(X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y →
      clos_refl_trans_1n R y z →
      clos_refl_trans_1n R x z.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma rsc_trans {α} {R : relation α} {x y z}
  (hxy : clos_refl_trans_1n R x y) (hyz : clos_refl_trans_1n R y z)
  : clos_refl_trans_1n R x z :=
begin
  induction hxy,
  case rt1n_refl { exact hyz, },
  case rt1n_trans : x' y' z' hxy' hyz' ih {
    exact rt1n_trans hxy' (ih hyz),
  },
end

/-
Theorem rtc_rsc_coincide :
         ∀(X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y ↔ clos_refl_trans_1n R x y.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem rtc_rsc_coincide {α} (R : relation α) (x y)
  : clos_refl_trans R x y ↔ clos_refl_trans_1n R x y :=
begin
  split,
    intro h,
    induction h,
    case rt_step : x' y' h' { exact rsc_R h', },
    case rt_refl { exact rt1n_refl h, },
    case rt_trans : x' y' z' hxy hyz ihy ihz {
      exact rsc_trans ihy ihz,
    },
  intro h,
  induction h,
  case rt1n_refl { exact rt_refl h },
  case rt1n_trans : x' y' z' hxy hyz ih {
    exact rt_trans (rt_step hxy) ih,
  },
end