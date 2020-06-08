import data.nat.basic

def mul (n m : ℕ) : ℕ :=
  nat.rec_on m
    0
    (λ _ m, n + m)

#reduce mul 2 5

#print nat.rec
#print nat.rec_on
#print nat.cases_on

def sub (n m : ℕ) : ℕ :=
  nat.rec_on m
    n
    (λ _ n, n - 1)

#reduce sub 0 2
#reduce sub 2 0
#reduce sub 10 15
#reduce sub 15 10

def exp (n m : ℕ) : ℕ :=
  nat.rec_on m
    1
    (λ _ n', mul n n')

#reduce exp 2 0
#reduce exp 3 3

variable {α : Type}

local attribute [simp]
def len (xs : list α) : ℕ :=
  list.rec_on xs
    0
    (λ _ _ l, 1 + l)

local attribute [simp]
def rev (xs : list α) : list α :=
  list.rec_on xs
    []
    (λ x _ r, r ++ [x]) /- too lazy to do this right -/

#reduce rev [1,2,3]

local attribute [simp]
theorem len_cons (x : α) (xs : list α) :
  len (x::xs) = 1 + len xs := by simp

local attribute [simp]
theorem len_app (s : list α) (t : list α) :
  len (s ++ t) = len s + len t := by induction s; simp [*, add_assoc]

theorem len_rev (as : list α) :
  len (rev as) = len as :=
begin
  induction as with a as ih,
    refl,
  have : len (rev (a :: as)) = len (rev as ++ [a]), by refl,
  rw this,
  rw len_app,
  rw ih,
  simp [ih, add_comm]
end

inductive data
| const : ℕ → data
| var : ℕ → data
| plus : data → data → data
| times : data → data → data

open list
open data

def eval (d: data) (v : list ℕ) : option ℕ :=
begin
  induction d,
    case const : n { exact n },
    case var : n { exact v.nth n },
    case plus : _ _ s t { exact do s ← s, t ← t, return (s + t) },
    case times : _ _ s t { exact s >>= (λ s, t.map (λ t, s * t)) },
end

#reduce eval (plus (const 1) (const 2)) []
#reduce eval (times (var 0) (plus (var 1) (var 2))) [2,3,5]