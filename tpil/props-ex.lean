variables p q r s : Prop

-- commutativity of ∧ and ∨
def ex1 : p ∧ q ↔ q ∧ p :=
begin
apply iff.intro; {
  intro h,
  exact ⟨h.right, h.left⟩
}
end

#print ex1

def ex2 : p ∨ q ↔ q ∨ p :=
begin
apply iff.intro; {
  intro h,
  cases h with hl hr,
    exact or.inr hl,
  exact or.inl hr,
}
end

#print ex2

-- associativity of ∧ and ∨
def ex3 : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
apply iff.intro; {
  intro h,
  rw and.assoc at *,
  exact h
}
end

#print ex3

def ex4 : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
apply iff.intro; {
  intro h,
  rw or.assoc at *,
  exact h
}
end

#print ex4

-- distributivity
def ex5 : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
apply iff.intro,
  intro h,
  cases h with hp hqr,
  cases hqr with hq hr,
    exact or.inl ⟨hp, hq⟩,
  exact or.inr ⟨hp, hr⟩,
intro h,
  split,
  cases h, repeat { exact h.left },
cases h with hpq hpr,
  exact or.inl hpq.right,
exact or.inr hpr.right
end

#print ex5

def ex6 : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
begin
apply iff.intro,
  intro h,
  split,
    cases h with hp hqr,
      exact or.inl hp,
    exact or.inr hqr.left,
  cases h with hp hqr,
    exact or.inl hp,
  exact or.inr hqr.right,
intro h,
cases h with hpq hpr,
cases hpq with hp hq,
  exact or.inl hp,
cases hpr with hp hr,
  exact or.inl hp,
exact or.inr ⟨hq, hr⟩
end

#print ex6

-- other properties
def ex7  : (p → (q → r)) ↔ (p ∧ q → r) :=
begin
apply iff.intro,
  intros h hp,
  exact h hp.left hp.right,
intros h hp hq,
exact h ⟨hp, hq⟩
end

#print ex7

def ex8 : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
begin
apply iff.intro,
  intro h,
  split,
    intro hp,
    exact h (or.inl hp),
  intro hq,
   exact h (or.inr hq),
intro h,
intro hpq,
cases hpq with hp hq,
  exact h.left hp,
exact h.right hq
end

#print ex8

def ex9 : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
apply iff.intro,
  intro h,
  split,
  by_contradiction,
    exact absurd (or.inl a) h,
  by_contradiction,
  exact absurd (or.inr a) h,
intro h,
by_contradiction,
  cases h with hp hq,
  cases a with hap haq,
  contradiction,
contradiction
end

#print ex9

def ex10 : ¬p ∨ ¬q → ¬(p ∧ q) :=
begin
intro h,
by_contradiction,
cases h with hnp hnq,
  exact absurd a.left hnp,
exact absurd a.right hnq
end


#print ex10

def ex11 : ¬(p ∧ ¬p) :=
begin
by_contradiction h,
cases h with hp hnp,
contradiction
end

#print ex11

def ex12 : p ∧ ¬q → ¬(p → q) :=
begin
intro h,
cases h with hp hnq,
by_contradiction,
exact absurd (a hp) hnq
end

#print ex12

def ex13 : ¬p → (p → q) :=
begin
intros hnp hp,
contradiction
end

#print ex13

def ex14 : (¬p ∨ q) → (p → q) :=
begin
intros h hp,
cases h with hnp hq,
  contradiction,
exact hq
end

#print ex14

def ex15 : p ∨ false ↔ p :=
begin
apply iff.intro,
  intro h,
  cases h with hp hf,
    exact hp,
  contradiction,
intro h,
  exact or.inl h
end

#print ex15

def ex16 : p ∧ false ↔ false :=
begin
apply iff.intro,
  intro h,
  cases h with hp hf,
  exact hf,
intro h,
  contradiction
end

#print ex16

def ex17 : ¬(p ↔ ¬p) :=
begin
by_contradiction,
have hnp : ¬p,
  assume p,
  exact absurd p (a.elim_left p),
exact absurd (a.elim_right hnp) hnp
end

#print ex17

def ex18 : (p → q) → (¬q → ¬p) :=
begin
intros hpq hnq,
by_contradiction,
exact absurd (hpq a) hnq
end

#print ex18

open classical

def ex19 : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
begin
intro h,
cases (em p) with hp hnp,
  cases (h hp) with hr hs,
    exact or.inl (λ p, hr),
  exact or.inr (λ p, hs),
exact or.inl (λ p, absurd p hnp)
end

#print ex19

def ex20 : ¬(p ∧ q) → ¬p ∨ ¬q :=
begin
intro h,
cases (em p) with hp hnp,
  cases (em q) with hq hnq,
    have : (p ∧ q), exact ⟨hp, hq⟩,
    exact absurd this h,
  exact or.inr hnq,
exact or.inl hnp
end

#print ex20

def ex21 : ¬(p → q) → p ∧ ¬q :=
begin
intro h,
cases (em p) with hp hnp,
  split,
    exact hp,
  by_contradiction,
    have : (p → q), exact (λ p, a),
    contradiction,
have : (p → q), exact (λ p, absurd p hnp),
contradiction
end

#print ex21

def ex22 : (p → q) → (¬p ∨ q) :=
begin
intro hpq,
cases (em p) with hp hnp,
  exact or.inr (hpq hp),
exact or.inl hnp
end

#print ex22

def ex23 : (¬q → ¬p) → (p → q) :=
begin
intros hqp hp,
cases (em q) with hq hnq,
  exact hq,
exact absurd hp (hqp hnq)
end

#print ex23

def ex24 : p ∨ ¬p :=
begin
exact (em p)
end

#print ex24

def ex25 : (((p → q) → p) → p) :=
begin
intro h,
cases (em p) with hp hnp,
  exact hp,
have : p → q, exact λ p, absurd p hnp,
exact h this
end

#print ex25