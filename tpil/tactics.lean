import data.list.basic

section tactics

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact hp,
  apply and.intro,
  exact hq,
  exact hp
end

#print test

theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  ⟨hp, hq, hp⟩

theorem test'' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro hp; exact and.intro hq hp
end

theorem test''' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by exact and.intro hp (and.intro hq hp)

variables {p q : Prop} (hp : p) (hq : q)

include hp hq

example : p ∧ q ∧ p :=
begin
  apply and.intro hp,
  exact and.intro hq hp
end

omit hp hq

example : p ∧ q ∧ p :=
let hp := hp, hq := hq in
begin
  apply and.intro hp,
  exact and.intro hq hp
end

theorem distr (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    apply or.elim (and.right h),
      intro hq,
      apply or.inl,
      apply and.intro,
        exact and.left h,
      exact hq,
    intro hr,
    apply or.inr,
    apply and.intro,
      apply and.left h,
    exact hr,
  intro h,
  apply or.elim h,
    intro hpq,
    apply and.intro,
      exact and.left hpq,
    apply or.inl,
    exact and.right hpq,
  intro hpr,
  apply and.intro,
    exact and.left hpr,
  apply or.inr,
  exact and.right hpr
end

#print distr

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros a b c h₁ h₂,
  exact eq.trans (eq.symm h₂) h₁
end

variables x y z w : ℕ

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
begin
  apply eq.trans h₁,
  apply eq.trans h₂,
  -- exact h₃
  assumption
end

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
begin
  apply eq.trans,
  assumption,
  apply eq.trans,
  assumption,
  assumption
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  apply eq.trans,
  apply eq.symm,
  assumption,
  assumption
end

example (y : ℕ) : (λ x : ℕ, 0) y = 0 :=
begin
  refl
end

example (x : ℕ) : x ≤ x :=
begin
  refl
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  assumption,
  assumption
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  repeat { assumption }
end

example : ∃ a : ℕ, 5 = a :=
begin
  apply exists.intro,
  reflexivity
end

example : ∃ a : ℕ, a = a :=
begin
  fapply exists.intro,
  exact 0,
  reflexivity
end

example (x : ℕ) : x = x :=
begin
  revert x,
  -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y,
  -- goal is y : ℕ ⊢ y = y
  reflexivity
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert h,
  -- goal is x y : ℕ ⊢ x = y → y = x
  intro h₁,
  -- goal is x y : ℕ, h₁ : x = y ⊢ y = x
  symmetry,
  assumption
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert x,
  -- goal is y : ℕ ⊢ ∀ (x : ℕ), x = y → y = x
  intros,
  symmetry,
  assumption
end

example : 3 = 3 :=
begin
  generalize : 3 = x,
  -- goal is x : ℕ ⊢ x = x,
  revert x,
  -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y, reflexivity
end

example : 2 + 3 = 5 :=
begin
  generalize h : 3 = x,
  -- goal is x : ℕ, h : 3 = x ⊢ 2 + x = 5,
  rw ←h
end

example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
  -- case hp : p
    right,
    exact hp,
  -- case hq : q
  left,
  exact hq
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  constructor,
    exact hq,
  exact hp
end

theorem distr' (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  constructor,
    intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
      left,
      constructor,
        assumption,
      assumption,
    right,
    constructor,
      assumption,
    assumption,
  intro h,
  cases h with hpq hpr,
    cases hpq with hp hq,
    constructor,
      assumption,
    left,
    assumption,
  cases hpr with hp hr,
  constructor,
    assumption,
  right,
  assumption
end

#print distr'

/- distr -/
theorem distr'' : ∀ (p q r : Prop), p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r :=
λ (p q r : Prop),
  {mp := λ (h : p ∧ (q ∨ r)),
           or.elim h.right (λ (hq : q), or.inl ⟨h.left, hq⟩) (λ (hr : r), or.inr ⟨h.left, hr⟩),
   mpr := λ (h : p ∧ q ∨ p ∧ r),
            or.elim h (λ (hpq : p ∧ q), ⟨hpq.left, or.inl hpq.right⟩)
              (λ (hpr : p ∧ r), ⟨hpr.left, or.inr hpr.right⟩)}

/- distr' -/
theorem distr''' : ∀ (p q r : Prop), p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r :=
λ (p q r : Prop),
  {mp := λ (h : p ∧ (q ∨ r)),
           and.dcases_on h
             (λ (hp : p) (hqr : q ∨ r),
                or.dcases_on hqr (λ (hq : q), or.inl ⟨hp, hq⟩) (λ (hr : r), or.inr ⟨hp, hr⟩)),
   mpr := λ (h : p ∧ q ∨ p ∧ r),
            or.dcases_on h (λ (hpq : p ∧ q), and.dcases_on hpq (λ (hp : p) (hq : q), ⟨hp, or.inl hq⟩))
              (λ (hpr : p ∧ r), and.dcases_on hpr (λ (hp : p) (hr : r), ⟨hp, or.inr hr⟩))}

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor,
  left,
    assumption
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  existsi x,
  left,
  assumption
end

universes u v

def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
begin
  intro p,
  cases p with pa pb,
  constructor,
  repeat {assumption}
end

def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
begin
  intro p,
  cases p with pa pb,
    right,
    assumption,
  left,
  assumption
end

open nat

example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) : P m :=
begin
  cases m with m',
    assumption,
  exact h₁ m'
end

example (p q : Prop) : p ∧ ¬p → q :=
begin
  intro h,
  cases h,
  contradiction
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  exact
    have hp : p, from h.left,
    have hqr : q ∨ r, from h.right,
    show (p ∧ q) ∨ (p ∧ r),
    begin
      cases hqr with hq hr,
        exact or.inl ⟨hp, hq⟩,
      exact or.inr ⟨hp, hr⟩
    end
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  constructor,
    intro h,
    cases h.right with hq hr,
      exact or.inl ⟨h.left, hq⟩,
    exact or.inr ⟨h.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    exact ⟨hpq.left, or.inl hpq.right⟩,
  exact ⟨hpr.left, or.inr hpr.right⟩
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    show (p ∧ q) ∨ (p ∧ r),
    cases h.right with hq hr,
      from or.inl ⟨h.left, hq⟩,
      from or.inr ⟨h.left, hr⟩,
  intro h,
  show (p ∧ (q ∨ r)),
  { cases h with hpq hpr,
    from ⟨hpq.left, or.inl hpq.right⟩,
    from ⟨hpr.left, or.inr hpr.right⟩ }
end

example (n : ℕ) : n + 1 = nat.succ n :=
begin
  show nat.succ n = nat.succ n,
  reflexivity
end

example (n : ℕ) : n + 1 = nat.succ n :=
begin
  reflexivity
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split,
  show p, from hp,
  show q, from hq
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    have hpq : p ∧ q,
      from ⟨hp, hq⟩,
    left,
    assumption,
  have : p ∧ r,
    split; assumption,
  right, exact this
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  have hp := h.left,
  have hqr := h.right,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    exact or.inl ⟨hp, hq⟩,
  exact or.inr ⟨hp, hr⟩
end

example : ∃ x, x + 2 = 8 :=
begin
  let a : ℕ := 3 * 2,
  existsi a,
  reflexivity
end

example : ∃ x, x + 2 = 8 := by
{ let a : ℕ := 3 * 2,
  existsi a,
  reflexivity }

meta def my_tac : tactic unit :=
`[ repeat { {left, assumption} <|> right <|> assumption } ]

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by my_tac
example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by my_tac
example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by my_tac

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
by split; try {split}; assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
begin
  split,
  all_goals { try {split} },
  all_goals { assumption }
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
by repeat { any_goals { split <|> assumption} }

variables (f : ℕ → ℕ) (a k : ℕ)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
begin
  rw h₂, -- replace k with 0
  rw h₁  -- replace f 0 with 0
end

example (x y : ℕ) (p : ℕ → Prop) (q : Prop) (h : q → x = y)
  (h' : p y) (hq : q) : p x :=
by {
  rw h hq,
  assumption
}

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_comm b, ←add_assoc]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_assoc, add_comm b]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_assoc, add_comm _ b]
end

example (h : a + 0 = 0) : f a = f 0 :=
by {
  rw add_zero at h,
  rw h
}

def tuple (α : Type u) (n : ℕ) :=
  { l : list α // list.length l = n }

variables {α : Type u} {n : ℕ}

example (h : n = 0) (t : tuple α n) : tuple α 0 :=
begin
  rw h at t,
  exact t
end

example {α : Type u} [ring α] (a b c : α) :
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
begin
  rw [
    mul_zero,
    mul_zero,
    zero_mul,
    zero_mul
  ],
  repeat {
    rw add_zero
  }
end

example {α : Type u} [ring α] (a b c : α) :
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
by { repeat { rw mul_zero <|> rw zero_mul <|> rw add_zero } }

example {α : Type u} [ring α] (a b c : α) :
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
by { simp }

example {α : Type u} [group α] {a b : α} (h : a * b = 1) :
  a⁻¹ = b :=
by rw [
  ←(mul_one a⁻¹),
  ←h,
  inv_mul_cancel_left
]

open list

example (xs : list ℕ) :
  reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs :=
by simp

end tactics

section local_attr

open list

variables (α : Type) (p : ℕ → Prop) (w x y z : ℕ)

local attribute [simp] add_comm mul_assoc mul_comm mul_left_comm

example (xs ys : list α) :
  length (reverse (xs ++ ys)) = length xs + length ys :=
by simp

example (h : p ((x + 0) * (0 + y * 1 + z * 0))) :
  p (x * y) :=
by {
  simp at h,
  assumption
}

example (h : p (x * y + z * w * x)) : p (x * w * z + y * x) :=
by { simp at *, assumption }

def f (m n : ℕ) : ℕ := m + n + m

example {m n : ℕ} (h : n = 1) (h' : 0 = m) : (f m n) = n :=
by simp [h, h'.symm, f]

example (u w x y z : ℕ) (h₁ : x = y + z) (h₂ : w = u + x) :
  w = z + y + u :=
by simp *

end local_attr

section simp

open list
universe u
variables {α : Type} (x y z : α) (xs ys zs : list α)

def mk_symm (xs : list α) := xs ++ reverse xs

theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by { unfold mk_symm, simp }

#print reverse_mk_symm

@[simp] theorem reverse_mk_symm' (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]

#print reverse_mk_symm'

example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp

example (xs ys : list ℕ) (p : list ℕ → Prop)
    (h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp at h; assumption

end simp

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {
  split,
  left,
  assumption,

  split,
  right,
  left,
  assumption,

  right,
  right,
  assumption
}

theorem foo (p q r s : Prop) (hp : p) :
(p ∨ q ∨ r ∨ s) ∧ (q ∨ p ∨ r ∨ s) ∧ (q ∨ r ∨ p ∨ s) ∧ (q ∨ r ∨ s ∨ p) :=
by { repeat { split <|> { try { left }, from hp } <|> right } }

#print foo

/- shorter for three. gets smoked at four -/
example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
⟨or.inl hp, or.inr (or.inl hp), or.inr (or.inr hp)⟩
