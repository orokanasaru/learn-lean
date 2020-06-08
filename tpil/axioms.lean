import data.nat.basic

namespace hidden

axiom propext {a b : Prop} : (a ↔ b) → a = b

section
  variables a b c d e : Prop
  variable p : Prop → Prop

  theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ iff.refl _

  theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

  #print axioms thm₁
end

universes u₁ u₂

#check (@funext : ∀ {α : Type u₁} {β : α → Type u₂}
           {f₁ f₂ : Π (x : α), β x},
         (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂)

universe u

def set (α : Type u) := α → Prop

namespace set

variable {α : Type u}

definition mem (x : α) (a : set α) := a x
notation e ∈ a := mem e a

theorem setext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
funext (assume x, propext (h x))

definition empty : set α := λ x, false
local notation `∅` := empty

definition inter (a b : set α) : set α := λ x, x ∈ a ∧ x ∈ b
notation a ∩ b := inter a b

theorem inter_self (a : set α) : a ∩ a = a :=
setext (assume x, and_self _)

theorem inter_empty (a : set α) : a ∩ ∅ = ∅ :=
setext (assume x, and_false _)

theorem empty_inter (a : set α) : ∅ ∩ a = ∅ :=
setext (assume x, false_and _)

theorem inter.comm (a b : set α) : a ∩ b = b ∩ a :=
setext (assume x, and_comm _ _)

end set

def f₁ (x : ℕ) := x
def f₂ (x : ℕ) := 0 + x

theorem feq : f₁ = f₂ := funext (assume x, (zero_add x).symm)

def val : ℕ := eq.rec_on feq (0 : ℕ)

-- complicated!
#reduce val

-- evaluates to 0
#eval val

namespace quotient

private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
(p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix `~` := eqv

open or

private theorem eqv.refl {α : Type u} :
  ∀ p : α × α, p ~ p :=
assume p, inl ⟨rfl, rfl⟩

private theorem eqv.symm {α : Type u} :
  ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
| (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) :=
    inl ⟨symm a₁b₁, symm a₂b₂⟩
| (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) :=
    inr ⟨symm a₂b₁, symm a₁b₂⟩

private theorem eqv.trans {α : Type u} :
  ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
| (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
  inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
| (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
  inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
| (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
  inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
| (a₁, a₂) (b₁, b₂) (c₁, c₂)
    (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
  inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

private theorem is_equivalence (α : Type u) :
  equivalence (@eqv α) :=
mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α)
  (@eqv.trans α)

instance uprod.setoid (α : Type u) : setoid (α × α) :=
setoid.mk (@eqv α) (is_equivalence α)

definition uprod (α : Type u) : Type u :=
quotient (uprod.setoid α)

namespace uprod
  definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
  ⟦(a₁, a₂)⟧

  local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂

theorem mk_eq_mk {α : Type} (a₁ a₂ : α) :
    {a₁, a₂} = {a₂, a₁} :=
  quot.sound (inr ⟨rfl, rfl⟩)

private definition mem_fn {α : Type} (a : α) :
    α × α → Prop
  | (a₁, a₂) := a = a₁ ∨ a = a₂

  -- auxiliary lemma for proving mem_respects
  private lemma mem_swap {α : Type} {a : α} :
    ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) := propext (iff.intro
      (λ l : a = a₁ ∨ a = a₂,
        or.elim l (λ h₁, inr h₁) (λ h₂, inl h₂))
      (λ r : a = a₂ ∨ a = a₁,
        or.elim r (λ h₁, inr h₁) (λ h₂, inl h₂)))

  private lemma mem_respects {α : Type} :
    ∀ {p₁ p₂ : α × α} (a : α),
      p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂) (b₁, b₂) a (inl ⟨a₁b₁, a₂b₂⟩) :=
    by { dsimp at a₁b₁, dsimp at a₂b₂, rw [a₁b₁, a₂b₂] }
  | (a₁, a₂) (b₁, b₂) a (inr ⟨a₁b₂, a₂b₁⟩) :=
    by { dsimp at a₁b₂, dsimp at a₂b₁, rw [a₁b₂, a₂b₁],
          apply mem_swap }

  def mem {α : Type} (a : α) (u : uprod α) : Prop :=
  quot.lift_on u (λ p, mem_fn a p) (λ p₁ p₂ e, mem_respects a e)

  local infix `∈` := mem

  theorem mem_mk_left {α : Type} (a b : α) : a ∈ {a, b} :=
  inl rfl

  theorem mem_mk_right {α : Type} (a b : α) : b ∈ {a, b} :=
  inr rfl

  theorem mem_or_mem_of_mem_mk {α : Type} {a b c : α} :
    c ∈ {a, b} → c = a ∨ c = b :=
  λ h, h


end uprod

end quotient

namespace choice

class inductive nonempty (α : Sort u) : Prop
| intro : α → nonempty

example (α : Type u) : nonempty α ↔ ∃ x : α, true :=
iff.intro (λ ⟨a⟩, ⟨a, trivial⟩) (λ ⟨a, h⟩, ⟨a⟩)

axiom choice {α : Sort u} : nonempty α → α

noncomputable theorem indefinite_description
    {α : Sort u} (p : α → Prop) :
  (∃ x, p x) → {x // p x} :=
λ h, choice (let ⟨x, px⟩ := h in ⟨⟨x, px⟩⟩)

noncomputable def some {a : Sort u} {p : a → Prop}
  (h : ∃ x, p x) : a :=
subtype.val (indefinite_description p h)

theorem some_spec {a : Sort u} {p : a → Prop}
  (h : ∃ x, p x) : p (some h) :=
subtype.property (indefinite_description p h)

noncomputable theorem inhabited_of_nonempty {α : Type u} :
  nonempty α → inhabited α :=
λ h, choice (let ⟨a⟩ := h in ⟨⟨a⟩⟩)


end choice

end hidden