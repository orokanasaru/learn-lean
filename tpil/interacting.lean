import data.nat.basic
import data.int.basic

section one
  variables x y : ℕ

  def double := x + x

  #check double
  #check double y
  #check double (2 * x)

  theorem t1 : double (x + y) = double x + double y :=
  by simp [double, add_left_comm, add_comm]

  #check t1 y
  #check t1 (2 * x)
end one

section two
  parameters {α : Type} (r : α → α → Type)
  parameter  transr : ∀ {x y z}, r x y → r y z → r x z

  variables {a b c d e : α}

  theorem t1' (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) : r a d :=
  transr (transr h₁ h₂) h₃

  theorem t2 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d)
      (h₄ : r d e) :
    r a e :=
  transr h₁ (t1' h₂ h₃ h₄)

  #check t1
  #check t2
end two

variable {α : Type*}

def is_prefix (l₁ : list α) (l₂ : list α) : Prop :=
∃ t, l₁ ++ t = l₂

/- this is just in lean now -/
-- infix `<+:`:50 := is_prefix

@[simp]
theorem list.is_prefix_refl (l : list α) : l <+: l :=
⟨[], by simp⟩

example : [1, 2, 3] <+: [1, 2, 3] := by simp

namespace int

def dvd (m n : ℤ) : Prop := ∃ k, n = m * k
instance : has_dvd int := ⟨int.dvd⟩

@[simp]
theorem dvd_zero (n : ℤ) : n ∣ 0 :=
⟨0, by simp⟩

theorem dvd_intro {m n : ℤ} (k : ℤ) (h : n = m * k) : m ∣ n :=
⟨k, h⟩

end int

open int

section mod_m
  parameter (m : ℤ)
  variables (a b c : ℤ)

  definition mod_equiv := (m ∣ b - a)

  local infix ≡ := mod_equiv

  theorem mod_refl : a ≡ a :=
  show m ∣ a - a, by simp [sub_self]

  theorem mod_symm (h : a ≡ b) : b ≡ a :=
  begin
    cases h with c hc,
    apply dvd_intro (-c),
    simp [eq.symm hc, neg_sub],
  end

  theorem mod_trans (h₁ : a ≡ b) (h₂ : b ≡ c) : a ≡ c :=
  begin
    cases h₁ with d hd, cases h₂ with e he,
    apply dvd_intro (d + e),
    simp [
      mul_add,
      eq.symm hd,
      eq.symm he,
      ←neg_add_eq_sub,
      ←add_assoc
    ],
    end
end mod_m

#check (mod_refl : ∀ (m a : ℤ), mod_equiv m a a)

#check (mod_symm : ∀ (m a b : ℤ), mod_equiv m a b →
                     mod_equiv m b a)

#check (mod_trans :  ∀ (m a b c : ℤ), mod_equiv m a b →
                       mod_equiv m b c → mod_equiv m a c)

variables m n : ℕ
variables i j : ℤ

#check i + m      -- i + ↑m : ℤ
#check i + m + j  -- i + ↑m + j : ℤ
#check i + m + n  -- i + ↑m + ↑n : ℤ

#check ↑m + i        -- ↑m + i : ℤ
#check ↑(m + n) + i  -- ↑(m + n) + i : ℤ
#check ↑m + ↑n + i   -- ↑m + ↑n + i : ℤ

#check of_nat

def foo {α : Type} (x : α) : α := x

#check foo
#check @foo
#reduce foo
#reduce (foo nat.zero)
#print foo

#print notation
#print notation + * -
#print +

#print axioms
#print options
#print prefix nat
#print prefix nat.le
#print classes
#print instances ring

#print fields ring
#print ring

#check (λ x, x + 1) 1
set_option pp.beta true
#check (λ x, x + 1) 1
set_option pp.beta false