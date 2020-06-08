open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) :=
λ z,
let ⟨y, iy⟩ := hg z,
    ⟨x, ix⟩ := hf y in
  ⟨x, show g(f(x)) = z, by simp *⟩

#print surjective_comp