import data.nat.basic
import tactic.basic

def foo : char → ℕ
| 'A' := 1
| 'B' := 2
| _   := 3

#print foo._main

inductive data
| const (n : ℕ) : data
| var (n : ℕ) : data
| plus s t : data
| times s t : data

open data

def eval (v : list ℕ): data → option ℕ
| (const n) := n
| (var n) := v.nth n
| (plus s t) := (eval s).bind (λ s, (eval t).map (λ t, s + t))
| (times s t) := (eval s).bind (λ s, (eval t).map (λ t, s * t))

#reduce eval [] (plus (const 1) (const 2))
#reduce eval [2,3,5] (times (var 0) (plus (var 1) (var 2)))

variable {α : Type}

/- this and the next makes simp way more powerful -/
local attribute [simp]
def len : list α → ℕ
| (x::xs) := 1 + len xs
| _ := 0

local attribute [simp]
def rev : list α → list α
| (x::xs) := rev xs ++ [x]
| _ := []

@[simp]
def rev' : list α → list α → list α
| [] r := r
| (x::xs) r := rev' xs (x::r)

@[simp]
def rev_tl (as : list α) : list α := rev' as []

-- @[simp]
-- lemma rev'_cons (a : α) (as : list α) (xs: list α):
--   rev' (a :: as) xs = rev' as (a::xs) := by induction as; simp

lemma rev'_app : ∀ as rs xs : list α,
  rev' as rs ++ xs = rev' as (rs ++ xs)
| [] _ _ := by simp
| _ _ [] := by simp
| (a::as) rs (x::xs) := by simp *

lemma rev_rev' (as : list α) : rev as = rev' as [] :=
begin
  induction as,
    simp *,
  unfold rev,
  unfold rev',
  rw as_ih,
  rw rev'_app,
  rw list.nil_append,
end

theorem tl_same (as : list α) : rev as = rev_tl as :=
by induction as; simp [rev_rev']

#reduce rev [1,2,3]

local attribute [simp]
theorem len_cons (x : α) (xs : list α) :
  len (x::xs) = 1 + len xs := by simp

local attribute [simp]
theorem len_app (s : list α) (t : list α) :
  len (s ++ t) = len s + len t := by induction s; simp [*, add_assoc]

theorem len_rev : ∀ as : list α, len (rev as) = len as
| (a::as) := by simp [*, add_comm]
| [] := rfl

theorem len_rev' (as : list α) : len (rev as) = len as :=
  by induction as; simp [*, add_comm]

open nat

theorem zero_add' : ∀ n, zero + n = n
| zero     := rfl
| (succ n) := congr_arg succ (zero_add' n)

#print acc

def nat_to_bin : ℕ → list ℕ
| 0       := [0]
| 1       := [1]
| (n + 2) :=
  have (n + 2) / 2 < n + 2, from sorry,
  nat_to_bin ((n + 2) / 2) ++ [n % 2]

#eval nat_to_bin 1234567

universe u

inductive vector (α : Type u) : nat → Type u
| nil {} : vector 0
| cons   : Π {n}, α → vector n → vector (n+1)

namespace vector
local notation h :: t := cons h t

#check @vector.cases_on
-- Π {α : Type}
--   {C : Π (a : ℕ), vector α a → Type}
--   {a : ℕ}
--   (n : vector α a),
--   (e1 : C 0 nil)
--   (e2 : Π {n : ℕ} (a : α) (a_1 : vector α n),
--           C (n + 1) (cons a a_1)),
--   C a n

local notation h :: t := cons h t

def tail_aux {α : Type} {n m : ℕ} (v : vector α m) :
    m = n + 1 → vector α n :=
vector.cases_on v
  (assume H : 0 = n + 1, nat.no_confusion H)
  (assume m (a : α) w : vector α m,
    assume H : m + 1 = n + 1,
      nat.no_confusion H (λ H1 : m = n, eq.rec_on H1 w))

def tail' {α : Type} {n : ℕ} (v : vector α (n+1)) :
  vector α n :=
tail_aux v rfl

def head {α : Type} : Π {n}, vector α (n+1) → α
| n (h :: t) := h

def tail {α : Type} : Π {n}, vector α (n+1) → vector α n
| n (h :: t) := t

lemma eta {α : Type} :
  ∀ {n} (v : vector α (n+1)), head v :: tail v = v
| n (h :: t) := rfl

def map {α β γ : Type} (f : α → β → γ) :
  Π {n}, vector α n → vector β n → vector γ n
| 0     nil       nil       := nil
| (n+1) (a :: va) (b :: vb) := f a b :: map va vb

#print map
#print map._main

def zip {α β : Type} :
  Π {n}, vector α n → vector β n → vector (α × β) n
| 0     nil       nil       := nil
| (n+1) (a :: va) (b :: vb) := (a, b) :: zip va vb

end vector

variable p : α → bool

def is_not_zero (m : ℕ) : bool :=
match m with
| 0     := ff
| (n+1) := tt
end

def filter : list α → list α
| []       := []
| (a :: l) :=
  match p a with
  |  tt := a :: filter l
  |  ff := filter l
  end

example : filter is_not_zero [1, 0, 0, 3, 0] = [1, 3] := rfl

def bar₁ : ℕ × ℕ → ℕ
| (m, n) := m + n

def bar₂ (p : ℕ × ℕ) : ℕ :=
match p with (m, n) := m + n end

def bar₃ : ℕ × ℕ → ℕ :=
λ ⟨m, n⟩, m + n

def bar₄ (p : ℕ × ℕ) : ℕ :=
let ⟨m, n⟩ := p in m + n