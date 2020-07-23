open tactic

namespace conj

variables a b : Prop

-- example : a → b → a ∧ b := by _

-- example : a → b → a ∧ b := by do
--   eh1 ← intro `h1,
--   eh2 ← intro `h2,
--   target >>= trace

-- example : a → b → a ∧ b := by do
--   eh1 ← intro `h1,
--   eh2 ← intro `h2,
--   local_context >>= trace

-- example : a → b → a ∧ b := by do
--   intro `h1,
--   intro `h2,
--   ea ← get_local `a,
--   eb ← get_local `b,
--   trace (to_string ea ++ ", " ++ to_string eb),
--   skip

example : a → b → a ∧ b := by do
  eh1 ← intro `h1,
  eh2 ← intro `h2,
  mk_const ``and.intro >>= apply,
    exact eh1,
  exact eh2

example : a → b → a ∧ b := by do
  eh1 ← intro `h1,
  eh2 ← intro `h2,
  applyc ``and.intro,
  exact eh1,
  exact eh2

example : a → b → a ∧ b :=
by do eh1 ← intro `h1,
      eh2 ← intro `h2,
      e ← to_expr ```(and.intro h1 h2),
      exact e

meta def my_tactic : tactic unit :=
do eh1 ← intro `h1,
   eh2 ← intro `h2,
   e ← to_expr ``(and.intro %%eh1 %%eh2),
   exact e

example : a → b → a ∧ b :=
by my_tactic

example (a b : Prop) (h : a ∧ b) : b ∧ a := by do
  split,
  to_expr ```(and.right h) >>= exact,
  to_expr ```(and.left h) >>= exact

namespace foo

theorem bar : true := trivial

meta def my_tac : tactic unit :=
mk_const ``bar >>= exact

example : true := by my_tac

end foo

example (a : Prop) : a → a :=
by do n ← mk_fresh_name,
      intro n,
      hyp ← get_local n,
      exact hyp

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do split,
   eh ← get_local `h,
   mk_mapp ``and.right [none, none, some eh] >>= exact,
   mk_mapp ``and.left [none, none, some eh] >>= exact

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do split,
      ea ← get_local `a,
      eb ← get_local `b,
      eh ← get_local `h,
      mk_app ``and.right [ea, eb, eh] >>= exact,
      mk_app ``and.left [ea, eb, eh] >>= exact

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do split,
      eh ← get_local `h,
      mk_app ``and.right [eh] >>= exact,
      mk_app ``and.left [eh] >>= exact

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do split,
      eh ← get_local `h,
      mk_const ``and.right >>= apply,
      exact eh,
      mk_const ``and.left >>= apply,
      exact eh


example (a b : Prop) (h : a ∧ b) : b ∧ a := by do
  split,
  to_expr ```(and.right h) >>= exact,
  to_expr ```(and.left h) >>= exact

example (a b : Prop) (h : a ∧ b) : b ∧ a := by do
  split,
  eh ← get_local `h,
  to_expr ``(and.right %%eh) >>= exact,
  to_expr ``(and.left %%eh) >>= exact

end conj

namespace hidden

meta def find_same_type : expr → list expr → tactic expr
| e []         := failed
| e (h :: hs) :=
  do t ← infer_type h,
     (unify e t >> return h) <|> find_same_type e hs

meta def assumption : tactic unit :=
do ctx ← local_context,
   t   ← target,
   h   ← find_same_type t ctx,
   exact h
<|> fail "assumption tactic failed"

meta def first {α : Type} : list (tactic α) → tactic α
| []      := fail "first tactic failed, no more alternatives"
| (t :: ts) := t <|> first ts

end hidden

meta def destruct_conjunctions : tactic unit :=
repeat (do
  l ← local_context,
  first $ l.map (λ h, do
    ht ← infer_type h >>= whnf,
    match ht with
    | `(and %%a %%b) := do
      n ← get_unused_name `h none,
      mk_mapp ``and.left [none, none, some h] >>= assertv n a,
      n ← get_unused_name `h none,
      mk_mapp ``and.right [none, none, some h] >>= assertv n b,
      clear h
    | _ := failed
    end))

namespace hidden

open nat

meta def repeat_at_most : nat → tactic unit → tactic unit
| 0        t := skip
| (succ n) t := (do t, repeat_at_most n t) <|> skip

meta def repeat : tactic unit → tactic unit :=
repeat_at_most 100000

end hidden

set_option pp.beta false

section
  variables {α : Type} (a b : α)

  example : (λ x : α, a) b = a :=
  by do goal ← target,
        match expr.is_eq goal with
        | (some (e₁, e₂)) := do trace e₁,
                                whnf e₁ >>= trace,
                                reflexivity
        | none            := failed
        end

  example : (λ x : α, a) b = a :=
  by do goal ← target,
        match expr.is_eq goal with
        | (some (e₁, e₂)) := do trace e₁,
                                whnf e₁ transparency.none >>= trace,
                                reflexivity
        | none            := failed
        end

  attribute [reducible]
  definition foo (a b : α) : α := a

  example : foo a b = a :=
  by do goal ← target,
        match expr.is_eq goal with
        | (some (e₁, e₂)) := do trace e₁,
                                whnf e₁ transparency.none >>= trace,
                                reflexivity
        | none            := failed
        end

  example : foo a b = a :=
  by do goal ← target,
        match expr.is_eq goal with
        | (some (e₁, e₂)) := do trace e₁,
                                whnf e₁ transparency.reducible >>= trace,
                                reflexivity
        | none            := failed
        end
end