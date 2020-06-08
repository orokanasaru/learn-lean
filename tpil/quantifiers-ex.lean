variables (α : Type) (p q : α → Prop)

def ex1 : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
begin
apply iff.intro,
  intro h,
  split,
    intro x,
    exact (h x).left,
  intro x,
  exact (h x).right,
intro h,
intro x,
  cases h with hp hq,
  exact ⟨hp x, hq x⟩
end

#print ex1

def ex2 : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
begin
intros hpq hp x,
exact hpq x (hp x)
end

#print ex2

def ex3 : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
intros h x,
cases h with hp hq,
  exact or.inl (hp x),
exact or.inr (hq x)
end

#print ex3

variables (men : Type) (barber : men)
variable (shaves : men → men → Prop)

def ex4 (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
begin
have c, from h barber,
have hns : ¬ shaves barber barber,
  assume hs : shaves barber barber,
  exact absurd hs (c.elim_left hs),
exact absurd (c.elim_right hns) hns
end

#print ex4