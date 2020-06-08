import data.nat.basic

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

#check weekday.sunday
#check weekday.monday

open weekday

#check sunday
#check monday

#check weekday.rec
#check weekday.rec_on
#check weekday.cases_on

namespace weekday
  @[reducible]
  private def cases_on := @weekday.cases_on

  def number_of_day (d : weekday) : nat :=
  cases_on d 1 2 3 4 5 6 7

 def next (d : weekday) : weekday :=
  weekday.cases_on d monday tuesday wednesday thursday friday
    saturday sunday

  def previous (d : weekday) : weekday :=
  weekday.cases_on d saturday sunday monday tuesday wednesday
    thursday friday

  #reduce next (next tuesday)
  #reduce next (previous tuesday)

  example : next (previous tuesday) = tuesday := rfl

  theorem next_previous (d: weekday) : next (previous d) = d :=
    by apply weekday.cases_on d; refl
end weekday

#reduce weekday.number_of_day weekday.sunday

open weekday (renaming cases_on → cases_on)

#reduce number_of_day sunday
#check cases_on

#check @nat.cases_on
#check @nat.rec_on

open nat

theorem zero_add' (n : ℕ) : 0 + n = n :=
nat.rec_on n rfl (λ n ih, by rw [add_succ, ih])

theorem zero_add'' (n : ℕ) : 0 + n = n :=
begin
apply n.rec_on,
  refl,
intros n ih,
calc
  0 + succ n = succ (0 + n) : rfl
  ... = succ n : by rw ih
end

theorem zero_add''' (n : ℕ) : 0 + n = n :=
begin
apply n.rec_on,
  refl,
intros n ih,
have : 0 + succ n = succ (0 + n),
  refl,
rw this,
rw ih
end


theorem add_assoc'' (m n k : ℕ) : m + n + k = m + (n + k) :=
begin
apply k.rec_on,
  refl,
intros k ih,
calc
  m + n + succ k = succ (m + n + k) : rfl
  ... = succ (m + (n + k)) : by rw ih
end

#print add_succ


theorem succ_add' (m n : nat) : succ m + n = succ (m + n) :=
begin
apply n.rec_on,
  refl,
intros n ih,
rw add_succ,
rw ih
end

theorem add_comm' (m n : nat) : m + n = n + m :=
begin
apply n.rec_on,
  rw add_zero,
  rw zero_add,
intros n ih,
rw succ_add',
rw ←ih
end

#check @list.rec
#check @list.rec_on

universe u

inductive list' (α : Type u)
| nil {} : list'
| cons : α → list' → list'

namespace list'

notation `⦃` l:(foldr `,` (h t, cons h t) nil) `⦄` := l

section
  open nat
  #check ([1, 2, 3, 4, 5] : list int)
end

end list'

variable p : ℕ → Prop

example (hz : p 0) (hs : ∀ n, p (succ n)) : ∀ n, p n :=
begin
  intro n,
  cases n,
  { exact hz },  -- goal is p 0
  apply hs       -- goal is a : ℕ ⊢ p (succ a)
end

example (n : ℕ) (h : n ≠ 0) : succ (pred n) = n :=
begin
  cases n with m,
  -- first goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    { apply (absurd rfl h) },
  -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ a)) = succ a
  reflexivity
end


example (hz : p 0) (hs : ∀ n, p (succ n)) (m k : ℕ) :
  p (m + 3 * k) :=
begin
  cases (m + 3 * k),
  { exact hz },  -- goal is p 0
  apply hs       -- goal is a : ℕ ⊢ p (succ a)
end

theorem zero_add_t (n : ℕ) : 0 + n = n :=
begin
induction n,
  case succ : n ih {
    rw add_succ,
    rw ih
  },

  case zero {
    refl
  }
end

example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) :
  n + k = m + k :=
begin
  injection h with h',
  injection h' with h'',
  rw h''
end

example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) :
  n + k = m + k :=
begin
  injections with h' h'',
  rw h''
end

example (m n : ℕ) (h : succ m = 0) : n = n + 7 :=
by injections

example (m n : ℕ) (h : succ m = 0) : n = n + 7 :=
by contradiction

example (h : 7 = 4) : false :=
by injections

mutual inductive even, odd
with even : ℕ → Prop
| even_zero : even 0
| even_succ : ∀ n, odd n → even (n + 1)
with odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)

#print even
#print odd