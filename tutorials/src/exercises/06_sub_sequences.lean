import tuto_lib
/-
This file continues the elementary study of limits of sequences.
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub (x y : ℝ) : |x - y| = |y - x|

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

and the definition:

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

You can also use a property proved in the previous file:

unique_limit : seq_limit u l → seq_limit u l' → l = l'

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m
-/


variable { φ : ℕ → ℕ}

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]) },
end

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
-- 0039
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros h n n',
  generalize hm : max n n' = m,
  cases ge_max_iff.mp (ge_of_eq (eq.symm hm)) with hn hn',
  use m,
  split,
    exact hn',
  calc φ m ≥ m : id_le_extraction' h m
       ... ≥ n : hn,
end

/-- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
-/

variables {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but displays it as the confusing:
`∃ (n : ℕ) (H : n ≥ N)`
One gets used to it. Alternatively, one can get rid of it using the lemma
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
-- 0040
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros h ε ε_pos n,
  rcases h with ⟨φ, φ_ext, φ_lim⟩,
  cases φ_lim ε ε_pos with n₂ hn₂, clear φ_lim,
  rcases extraction_ge φ_ext n n₂ with ⟨n₃, hn₃, hφ₃⟩,
  exact ⟨φ n₃, hφ₃, hn₂ n₃ hn₃⟩,
end

/-
The above exercice can be done in five lines.
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/

/-- If `u` tends to `l` then its subsequences tend to `l`. -/
-- 0041
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with n hn, clear h,
  use n,
  intros n₂ hn₂,
  apply hn,
  calc φ n₂ ≥ n₂ : id_le_extraction' hφ n₂
       ...  ≥ n  : hn₂,
end

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
-- 0042
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  rcases ha with ⟨φ, φ_ext, φ_lim⟩,
  have φ_lim', exact subseq_tendsto_of_tendsto' hl φ_ext,
  exact unique_limit φ_lim φ_lim',
end

/-- Cauchy_sequence sequence -/
def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  rintro ⟨l, h⟩,
  intros ε ε_pos,
  cases h (ε/2) (by linarith) with n hn,
  use n,
  intros p q hp hq,
  replace hp, exact hn p hp,
  replace hq, exact hn q hq,
  calc |u p - u q| = |(u p - l) + (l - u q)| : by ring
       ...         ≤ |u p - l| + |l - u q|   : by apply abs_add
       ...         = |u p - l| + |u q - l|   : by rw abs_sub (u q)
       ...         ≤ ε                       : by linarith,
end

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/
-- 0044
example (hu : cauchy_sequence u) (hl : cluster_point u l) : seq_limit u l :=
begin
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with n hn,
  rcases near_cluster hl (ε/2) (by linarith) n with ⟨p, hp₁, hp₂⟩,
  use n,
  intros q hq,
  specialize hn p q hp₁ hq,
  calc |u q - l| = |(u q - u p) + (u p - l)| : by ring
       ...       ≤ |u q - u p| + |u p - l|   : by apply abs_add
       ...       = |u p - u q| + |u p - l|   : by rw abs_sub (u q)
       ...       ≤ ε                         : by linarith,
end

