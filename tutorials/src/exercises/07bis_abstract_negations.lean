import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,
    intros h hnq hnp,
    exact hnq (h hnp),
  intros h p,
  by_contradiction hnq,
  exact h hnq p,
end

-- 0056
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  split,
    intros h,
    by_contradiction c,
    apply h,
    intro hp,
    by_contradiction c',
    apply c,
    exact ⟨hp, c'⟩,
  rintro ⟨hp, hnq⟩ h,
  exact hnq (h hp),
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  split,
    intro h,
    apply propext,
    split,
      intro p,
      exact h p,
    intro c,
    exfalso,
    exact c,
  intro h,
  rw h,
  exact id,
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split,
    intro h,
    by_contradiction c,
    apply h,
    intro x,
    by_contradiction c',
    apply c,
    use x,
  rintros ⟨x, hx⟩ h,
  exact hx (h x),
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  split,
    intros h x,
    by_contradiction c,
    apply h,
    use [x, c],
  rintro h ⟨x, hc⟩,
  exact h x hc,
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  split,
    intros h ε ε_pos c,
    apply h,
    use [ε, ε_pos, c],
  rintro h ⟨ε, ε_pos, c⟩,
  exact h ε ε_pos c,
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  split,
    intro h,
    by_contradiction c,
    apply h,
    intros x hx,
    by_contradiction c',
    apply c,
    use [x, hx, c'],
  rintro ⟨x, hx, hx'⟩ c,
  exact hx' (c x hx),
end

end negation_quantifiers

