import data.nat.basic

section universal
variables (α : Type) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
assume h : ∀ x : α, p x ∧ q x,
assume y: α,
show p y, from (h y).left

variable r : α → α → Prop
variable trans_r : ∀ {x y z}, r x y → r y z → r x z

variables a b c : α
variables (hab : r a b) (hbc : r b c)

#check trans_r
#check @trans_r a b c
#check trans_r hab
#check trans_r hab hbc
#check @trans_r a b c hab hbc

variable refl_r : ∀ x, r x x
variable symm_r : ∀ {x y}, r x y → r y x

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
end universal

section equality
universe u

#check @eq.refl.{u}
#check @eq.symm.{u}
#check @eq.trans.{u}

variables (α β : Type u) (a b c d: α)
variables (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d := (hab.trans hcb.symm).trans hcd

example (f : α → β) (a : α) : (λ x, f x) a = f a := eq.refl _
example : 2 + 3 = 5 := rfl

example (α : Type u) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  eq.subst h1 h2

example (α : Type u) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variables f g : α → ℕ
variable h₁ : a = b
variable h₂ : f = g

example : f a = f b := congr_arg f h₁
example : f a = g a := congr_fun h₂ a
example : f a = g b := congr h₂ h₁

variables (x y z : ℤ)

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
  from mul_add (x + y) x y,
have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
  from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm

end equality

section calculate

variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

theorem T : a = e :=
calc
  a = b : h1
  ... = c + 1 : h2
  ... = d + 1 : congr_arg _ h3
  ... = 1 + d : add_comm d (1 : ℕ)
  ... = e : eq.symm h4

include h1 h2 h3 h4
theorem T' : a = e :=
calc
  a = b : by rw h1
  ... = c + 1 : by rw h2
  ... = d + 1 : by rw h3
  ... = 1 + d : by rw add_comm
  ... = e : by rw h4

theorem T'' : a = e := by rw [h1, h2, h3, add_comm, h4]

theorem T''' : a = e := by simp [add_comm, h1, h2, h3, h4]

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by rw [mul_add, add_mul, add_mul, ←add_assoc]

-- example (x y : ℕ) :
--   (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
-- by simp [mul_add, ←add_assoc]

end calculate

section existential

open nat

example : ∃ x : ℕ, x > 0 :=
have h : 1 > 0, from zero_lt_succ 0,
exists.intro 1 h

#check @exists.intro

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

variable g : ℕ → ℕ → ℕ
variable hg : g 0 0 = 0

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.implicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
  (assume w,
    assume hw : p w ∧ q w,
    show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hw⟩ :=
  ⟨w, hw.right, hw.left⟩
end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hpw, hqw⟩ :=
  ⟨w, hqw, hpw⟩
end

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩

def is_even (a : nat) := ∃ b, a = 2 * b

theorem even_plus_even {a b : nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
exists.elim h1 (assume w1, assume hw1 : a = 2 * w1,
exists.elim h2 (assume w2, assume hw2 : b = 2 * w2,
exists.intro (w1 + w2)
  (calc
    a + b = 2 * w1 + 2 * w2 : by rw [hw1, hw2]
    ... = 2 * (w1 + w2) : by rw mul_add)))

theorem even_plus_even' {a b : nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
match h1, h2 with
  ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
end

variable a : α
variable r : Prop

open classical

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
  (assume ⟨a, (h : p a ∨ q a)⟩,
    or.elim h
      (assume hp : p a, or.inl ⟨a, hp⟩)
      (assume hq : q a, or.inr ⟨a, hq⟩)
  )
  (assume h : (∃ x, p x) ∨ (∃ x, q x),
    or.elim h
      (assume ⟨a, (h : p a)⟩, ⟨a, (or.inl h)⟩)
      (assume ⟨a, (h : q a)⟩, ⟨a, (or.inr h)⟩)
  )

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro
  (assume ⟨b, (hb : p b → r)⟩,
    assume h2 : ∀ x, p x,
    show r, from  hb (h2 b))
  (assume h1 : (∀ x, p x) → r,
    show ∃ x, p x → r, from
      by_cases
        (assume hap : ∀ x, p x, ⟨a, (λ _, h1 hap)⟩)
        (assume hnap : ¬ ∀ x, p x,
          by_contradiction
            (assume hnex : ¬ ∃ x, p x → r,
              have hap : ∀ x, p x, from
                assume x,
                by_contradiction
                  (assume hnp : ¬ p x,
                    have hex : ∃ x, p x → r,
                      from ⟨x, (assume hp, absurd hp hnp)⟩,
                    show false, from hnex hex),
              show false, from hnap hap)))

end existential
