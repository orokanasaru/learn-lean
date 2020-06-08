import system.io
open io nat

def hello_world : io unit :=
put_str_ln "hello world"

def print_squares : ℕ → io unit
| 0 :=return ()
| (succ n) := print_squares n >>
              put_str_ln (
                to_string n ++ "^2 = " ++
                to_string (n * n))

#eval hello_world
#eval print_squares 20
#print axioms hello_world

-- BEGIN
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
assume hpq : p ∧ q,
have hp : p, from and.left hpq,
have hq : q, from and.right hpq,
show q ∧ p, from and.intro hq hp
-- END

constant m : ℕ
constant n : ℕ
constants b1 b2 : bool

/- whoo -/
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check tt


constant f : ℕ → ℕ
constant p : ℕ × ℕ
#check p.2
#check (f, p).1
#check f p.1

#check ℕ
#check Type
#check (×)

universe u
constant α  : Type u
#check α
#check Type u

#check λ x, x + 5

#check λ (α β : Type) (b : β) (x : α), x
#check (λ (α β : Type) (b : β) (x : α), x) ℕ

#reduce (λ x, x) f
#reduce (λ x, α) f

#reduce b1 || tt
#reduce tt || b1

#reduce n * 0
#reduce n * 1

#eval 12345 * 54321

def foo : (ℕ → ℕ) → ℕ := λ f, f 0
#check foo
#print foo

def double (x : ℕ) : ℕ := x + x
def doubl' := λ x : ℕ, x + x

#check double = doubl'
#reduce double = doubl'

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ
  :=  λ a b, f (a, b)

#check let y := 2 + 2 in y * y

section useful
  variables (α β γ : Type)
  variables (g : β → γ) (f: α → β) (h : α → α)
  variable x : α

  def compose := g (f x)
  def do_twice := h (h x)
  def do_thrice :=  h (h (h x))
end useful

#print compose
#print do_twice
#print do_thrice

namespace foo
  def a : ℕ := 5
  #print a
end foo

#print foo.a

open foo

#print a

namespace hidden
universe μ

constant list: Type μ → Type μ
constant cons : Π α : Type μ, α → list α → list α

end hidden

open list
#check list
#check @cons
#check @nil
#check @head

variable α : Type
variable β : α → Type
variable a : α
variable b : β a

#check sigma.mk a b

namespace list
  constant cons' : Π {α : Type u}, α → list α → list α
#check cons'
end list

