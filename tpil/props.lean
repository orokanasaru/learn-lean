constants p q : Prop

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

#print t1

theorem t1' :  p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp

theorem t1'' (hp : p) (hq : q) : p := hp

axiom hp : p
theorem t2 :  q → p := t1 hp

theorem t1''' : ∀ (p q : Prop), p → q → p :=
  λ (p q : Prop) (hp : p) (hq : q), hp

variables p q r s : Prop

theorem t2' (h₁ : q → r) (h₂ : p → q) : p → r :=
  assume h₃ : p,
  show r, from h₁ (h₂ h₃)

example (hp : p) (hq : q) : p ∧ q := and.intro hp hq
#check assume (hp : p) (hq : q), and.intro hp hq

variables (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)

variable l : list ℕ
#check list.head l
#check l.head

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

example (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p, show q ∨ p, from or.intro_right q hp)
  (assume hq : q, show q ∨ p, from or.intro_left p hq)

example (h : p ∨ q) : q ∨ p :=
h.elim (assume hp : p, or.inr hp) (assume hq : q, or.inl hq)

example : (p → q) → ¬q → ¬p :=
assume hpq : p → q,
assume hnq : ¬q,
assume hp : p,
show false, from hnq (hpq hp)

/- false.elim -- absurd -/
/- true.elim -- trivial -/

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from and.intro (and.right h) (and.left h))
  (λ h, ⟨h.right, h.left⟩)

example (h : p ∧ q) : q ∧ p :=
have hp : p, from and.left h,
have hq : q, from and.right h,
show q ∧ p, from and.intro hq hp

example (h : p ∧ q) : q ∧ p :=
have hp : p, from and.left h,
suffices hq : q, from and.intro hq hp,
show q, from and.right h

section excluded_middle
open classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

#check em

example (h : ¬¬p) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, absurd h1 h)

example (h : ¬¬p) : p :=
by_contradiction
  (assume h1 : ¬p,
    show false, from h h1)

example (h : ¬¬p) : p :=
by_contradiction (λ h1, h h1)
end excluded_middle

-- theorem em' {p : Prop} : (¬¬p → p) → p ∨ ¬p :=
-- assume dne : ¬¬p → p,
-- assume hnnp : ¬¬p,
-- show p ∨ ¬p, from or.inl (dne hnnp)

example : p ∧ q ↔ q ∧ p :=
iff.intro
(λ hpq, ⟨hpq.right, hpq.left⟩)
(λ hqp, ⟨hqp.right, hqp.left⟩)

open classical

example : (¬q → ¬p) → (p → q) :=
assume h : ¬q → ¬p,
assume hp : p,
-- show q, from
--   by_contradiction
--     (assume hnq: ¬q,
--       show false, from absurd hp (h hnq))
by_contradiction (λ hnq, absurd hp (h hnq))
