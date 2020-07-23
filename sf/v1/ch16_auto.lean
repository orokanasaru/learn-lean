import tactic.basic
import tactic.omega
import tactic.tauto
import .ch11_imp

/-
Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: ∀c st st1 st2,
    st =[ c ]⇒ st1 →
    st =[ c ]⇒ st2 →
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; apply H1. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption. Qed.
-/

-- namespace tactic
-- open native

-- meta def names : list expr → tactic (list name) :=
-- λes, match es with
-- | [] := do pure []
-- | e :: es := do
--   es' ← names es,
--   pure $ e.local_pp_name :: es'
-- end

-- meta def inv (h : name) (ns : list name := []): tactic unit := do
--   h' ← get_local h,
--   rs ← cases h',
--   try $ clear_lst [h],
--   subst_vars,
--   g ← get_goals,
--   -- supporting naming
--   try $ (list.zip g rs).mmap'(λr, do
--     -- trace r,
--     let ⟨g, n, e⟩ := r,
--     n' ← names e,
--     rename_many (rb_map.of_list $ n'.zip ns)
--     -- trace r
--     -- try $ with_enable_tags $ set_main_tag [n]
--   )

-- end tactic

open interactive interactive.types lean.parser tactic

namespace tactic.interactive

meta def inv (h : parse ident) (w : parse with_ident_list): tactic unit :=
  propagate_tags $ do
  h' ← get_local h,
  rs ← cases (none, pexpr.of_expr h') w,
  try $ propagate_tags $ do
  clear_lst [h],
  subst_vars
  -- g ← get_goals,
  -- -- supporting naming
  -- try $ (list.zip g rs).mmap'(λr, do
  --   -- trace r,
  --   let ⟨g, n, e⟩ := r,
  --   n' ← names e,
  --   rename_many (rb_map.of_list $ n'.zip ns)
  --   -- trace r
  --   -- try $ with_enable_tags $ set_main_tag [n]
  -- )

end tactic.interactive

open imp imp.ceval

/-
inductive ceval : com → state → state → Prop
| E_Skip : ∀st, ceval SKIP st st
| E_Ass : ∀{st a₁ n} x,
  aeval st a₁ = n →
  ceval (x ::= a₁) st (x !→ n ; st)
| E_Seq : ∀{c₁ c₂ st st' st''},
  ceval c₁ st st' →
  ceval c₂ st' st'' →
  ceval (c₁ ;; c₂) st st''
| E_IfTrue : ∀{st st' b c₁} c₂,
  beval st b = tt →
  ceval c₁ st st' →
  ceval (TEST b THEN c₁ ELSE c₂ FI) st st'
| E_IfFalse : ∀{st st' b} c₁ {c₂},
  beval st b = ff →
  ceval c₂ st st' →
  ceval (TEST b THEN c₁ ELSE c₂ FI) st st'
| E_WhileFalse : ∀{b st} c,
  beval st b = ff →
  ceval (WHILE b DO c END) st st
| E_WhileTrue : ∀{st st' st'' b c},
  beval st b = tt →
  ceval c st st' →
  ceval (WHILE b DO c END) st' st'' →
  ceval (WHILE b DO c END) st st''

-/

/- it's horrible (like the coq version) -/
/-
TODO  i could make it less so with names since i improved the tactic
-/
theorem ceval_deterministic {c st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : st =[ c ]⇒ st₂)
  : st₁ = st₂ :=
begin
  induction h₁ generalizing st₂; inv h₂,
  case E_Ass { refl, },
  case E_Seq {
    cases h₁_ih_a h₂_a,
    exact h₁_ih_a_1 h₂_a_1,
  },
  case E_IfTrue E_IfTrue { exact h₁_ih h₂_a_1, },
  case E_IfTrue E_IfFalse {
    rw h₁_a at h₂_a,
    contradiction,
  },
  case E_IfFalse E_IfTrue {
    rw h₁_a at h₂_a,
    contradiction,
  },
  case E_IfFalse E_IfFalse { exact h₁_ih h₂_a_1, },
  case E_WhileFalse E_WhileTrue {
    rw h₁_a at h₂_a,
    contradiction,
  },
  case E_WhileTrue E_WhileFalse {
    rw h₁_a at h₂_a,
    contradiction,
  },
  case E_WhileTrue E_WhileTrue {
    cases h₁_ih_a h₂_a_1,
    exact h₁_ih_a_1 h₂_a_2,
  },
end

/-
Example auto_example_1 : ∀(P Q R: Prop),
  (P → Q) → (Q → R) → P → R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.
-/

example {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) (hp : P) : R :=
begin
  apply hqr,
  apply hpq,
  exact hp,
end

/-
Example auto_example_1' : ∀(P Q R: Prop),
  (P → Q) → (Q → R) → P → R.
Proof.
  auto.
Qed.
-/

example (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by tauto

/-
Example auto_example_2 : ∀P Q R S T U : Prop,
  (P → Q) →
  (P → R) →
  (T → R) →
  (S → T → U) →
  ((P→Q) → (P→S)) →
  T →
  P →
  U.
Proof. auto. Qed.
-/

/- tauto is not good -/
example (P Q R S T U : Prop) :
  (P → Q) →
  (P → R) →
  (T → R) →
  (S → T → U) →
  ((P → Q) → (P → S)) →
  T →
  P →
  U := by
begin
  intros,
  apply a_3; tauto,
end

/- cc destroys this though -/
example (P Q R S T U : Prop) :
  (P → Q) →
  (P → R) →
  (T → R) →
  (S → T → U) →
  ((P → Q) → (P → S)) →
  T →
  P →
  U := by cc

/-
Example auto_example_3 : ∀(P Q R S T U: Prop),
  (P → Q) →
  (Q → R) →
  (R → S) →
  (S → T) →
  (T → U) →
  P →
  U.
Proof.
  (* When it cannot solve the goal, auto does nothing *)
  auto.
  (* Optional argument says how deep to search (default is 5) *)
  auto 6.
Qed.
-/

/- no depth limit -/
/- tauto is kind of terrible -/
example (P Q R S T U : Prop) :
  (P → Q) →
  (Q → R) →
  (R → S) →
  (S → T) →
  (T → U) →
  P →
  U :=
begin
  intros,
  apply a_4,
  apply a_3,
  apply a_2,
  tauto,
end

/- again, cc ftw -/
example (P Q R S T U : Prop) :
  (P → Q) →
  (Q → R) →
  (R → S) →
  (S → T) →
  (T → U) →
  P →
  U := by cc

/-
Example auto_example_4 : ∀P Q R : Prop,
  Q →
  (Q → R) →
  P ∨ (Q ∧ R).
Proof. auto. Qed.
-/

/- tauto failed here too -/
example (P Q R : Prop) : Q → (Q → R) → P ∨ (Q ∧ R) := by cc

/-
Lemma le_antisym : ∀n m: nat, (n ≤ m ∧ m ≤ n) → n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : ∀n m p : nat,
  (n ≤ p → (n ≤ m ∧ m ≤ n)) →
  n ≤ p →
  n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.
-/

lemma le_antisym {n m : ℕ} (h : n ≤ m ∧ m ≤ n) : n = m := by finish

/- maybe not the best idea, but tauto can pick this up -/
-- local attribute [refl] le_antisym

/-
hint is dope
-/

/- le_antisym not needed -/
example (n m p : ℕ) :
  (n ≤ p → n ≤ m ∧ m ≤ n) →
  n ≤ p →
  n = m := by finish using [le_antisym] {classical := ff}

/-
Hint Resolve T.

Hint Constructors c.

Hint Unfold d.
-/

/-
seems like attribute refl or simp handles that
-/

/-
Hint Resolve le_antisym.

Example auto_example_6' : ∀n m p : nat,
  (n≤ p → (n ≤ m ∧ m ≤ n)) →
  n ≤ p →
  n = m.
Proof.
  intros.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: ∀x,
  (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x.
Proof.
  auto. (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : ∀x,
  (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x.
Proof. auto. Qed.
-/

/- clarify and safe work too -/
/- iversions don't use classical -/

/- hint was never needed -/
example (n m p : ℕ) :
  (n ≤ p → n ≤ m ∧ m ≤ n) →
  n ≤ p →
  n = m := by ifinish

def is_fortytwo (x) := x = 42

-- example (x) : (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x := by isafe,

example (x) : (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x := by isafe using is_fortytwo

local attribute [simp] is_fortytwo

example (x) : (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x := by finish

/-
Theorem ceval_deterministic': ∀c st st1 st2,
    st =[ c ]⇒ st1 →
    st =[ c ]⇒ st2 →
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
       induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.
-/

theorem ceval_deterministic' {c st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : st =[ c ]⇒ st₂)
  : st₁ = st₂ :=
begin
  induction h₁ generalizing st₂; inv h₂; try { ifinish },
  /- E_ASS -/ { tauto, },
  /- E_SEQ -/ {
    have : h₁_st' = h₂_st', tauto,
    ifinish,
  },
  /- E_WHILE_TRUE E_WHILE_TRUE -/ {
    have : h₁_st' = h₂_st', tauto,
    ifinish,
  },
end

/- not a lot of repetition above -/
/- it's horribly slow and obnoxious to run though -/

/-
Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Theorem ceval_deterministic'': ∀c st st1 st2,
    st =[ c ]⇒ st1 →
    st =[ c ]⇒ st2 →
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rwinv H H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rwinv H H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rwinv H H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rwinv H H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. Qed.
-/

namespace tactic.interactive

/-
TODO: use rewrite_rules, location, and with_ident_list
-/
meta def rwinv (h₁ h₂ : parse ident) : tactic unit :=
propagate_tags $ do
  h₁' ← get_local h₁,
  h₂' ← get_local h₂,
  rewrite_hyp h₁' h₂',
  inv h₂ []

end tactic.interactive

theorem ceval_deterministic'' {c st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : st =[ c ]⇒ st₂)
  : st₁ = st₂ :=
begin
  induction h₁ generalizing st₂; inv h₂; try { tauto <|> rwinv h₁_a h₂_a },
  case E_Seq {
    have : h₁_st' = h₂_st', tauto,
    ifinish,
  },
  case E_WhileTrue E_WhileTrue {
    have : h₁_st' = h₂_st', tauto,
    ifinish,
  },
end

/-
Ltac find_rwinv :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    ⊢ _ ⇒ rwinv H1 H2
  end.
-/

namespace tactic.interactive

-- meta def eq_bool (b : bool): list expr → tactic (option expr)
-- | [] := none
-- | (e :: es) := do
--   e' ← infer_type e,
--   match e' with
--   | `(_ = %%b') := if (reflect b).to_expr = b'
--                    then pure $ some e
--                    else eq_bool es
--   | _ := eq_bool es
--   end

meta def find_rwinv : tactic unit :=
do
  ctx ← local_context,
  mv ← mk_mvar,
  h₁ ← find_same_type `(%%mv = tt) ctx,
  h₂ ← find_same_type `(%%mv = ff) ctx,
  rwinv h₁.local_pp_name h₂.local_pp_name

end tactic.interactive

theorem ceval_deterministic''' {c st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : st =[ c ]⇒ st₂)
  : st₁ = st₂ :=
begin
  induction h₁ generalizing st₂; inv h₂; try { tauto <|> find_rwinv },
  case E_Seq {
    have : h₁_st' = h₂_st', tauto,
    ifinish,
  },
  case E_WhileTrue E_WhileTrue {
    have : h₁_st' = h₂_st', tauto,
    ifinish,
  },
end

/-
Ltac find_eqn :=
  match goal with
    H1: ∀x, ?P x → ?L = ?R,
    H2: ?P ?X
    ⊢ _ ⇒ rewrite (H1 X H2) in *
  end.
-/

/-
ltac is nice...
-/
namespace tactic.interactive

open expr binder_info

-- meta def expr_view : expr → tactic string := λe, do
--   trace $ "e: " ++ to_string e,
--   s ← match e with
--   | app e body :=
--     pure $ "app: " ++ to_string e ++ to_string body
--   | const n l := pure $ "const: " ++ to_string n ++ to_string l
--   | elet n e₁ e₂ body :=
--     pure $ "elet: " ++ to_string n ++ to_string e₁ ++
--       to_string e₂ ++ to_string body
--   | lam n bind e body :=
--     pure $ "lam: " ++ to_string n ++ to_string e ++ to_string body
--   | local_const n₁ n₂ bind e :=
--     pure $ "loc: " ++ to_string n₁ ++ to_string n₂ ++ to_string e
--   | macro d es := pure $ "mac: " ++ to_string es
--   | mvar n₁ n₂ e :=
--     pure $ "mvar: " ++ to_string n₁ ++ to_string n₂ ++ to_string e
--   | pi n bind e body :=
--     -- expr_view e >>= λe,
--     -- expr_view body >>= λbody,
--     pure $ "pi: " ++ to_string n ++ to_string e ++ to_string body
--   | sort l := pure $ "sort: " ++ to_string l
--   | var n := pure $ "var: " ++ to_string n
--   end,
--   trace s,
--   pure s

-- meta def ctx_view : tactic unit :=
-- do
--   ctx ← local_context,
--   ctx.mmap' (λh, expr_view h >> infer_type h >>= expr_view)

-- meta def infer (e : expr) : tactic (expr × expr) := do
--   e' ← infer_type e,
--   pure (e, e')

meta def find_pi : (list (expr × expr)) → tactic (list (expr × expr)) := λes,
  match es with
  | (n, (pi _ _ _ (pi _ _ (app e₁ e₂) `(%%l = %%r))))::es := do
    es ← find_pi es,
    pure $ (n, e₁)::es
  | (_ :: es) := find_pi es
  | _ := pure $ []
  end

meta def find_app (e: expr) : (list (expr × expr)) → tactic (list (expr × expr))
:= λes,
  match es with
  | (n, (app e₁ e₂))::es := do
    es ← find_app es,
    pure $ if e = e₁ then (n, e₂)::es else es
  | (_ :: es) := find_app es
  | _ := pure $ []
  end

meta def find_props : tactic (list (expr × expr × expr)) := do
  h ← local_context,
  h ← h.mmap (λh, do h' ← infer_type h, pure (h, h')),
  a ← find_pi h,
  p ← a.mmap (λ⟨n, e⟩, do
    p ← find_app e h,
    pure $ p.map (λ⟨n₁, e⟩, (n, n₁, e))
  ),
  pure p.join

meta def find_eqn : tactic unit :=
propagate_tags $ do
  p ← find_props,
  p.mmap' (λ⟨n₁, n₂, e⟩, do
    h ← note `this none (mk_app n₁ [e, n₂]),
    do tactic.subst h <|> tactic.clear h
  )

end tactic.interactive

/-
Theorem ceval_deterministic''''': ∀c st st1 st2,
    st =[ c ]⇒ st1 →
    st =[ c ]⇒ st2 →
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv;
    repeat find_eqn; auto.
Qed.
-/

/-
note: finish fails to find refl for E_ASS and find_eqn runs a loop internally
-/
theorem ceval_deterministic''''' {c st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : st =[ c ]⇒ st₂)
  : st₁ = st₂ :=
begin
  induction h₁ generalizing st₂;
    inv h₂;
    try { refl <|> find_rwinv };
    find_eqn;
    ifinish,
end

/-
Module Repeat.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).
-/

namespace repeat

inductive com
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c₁ c₂ : com)
| CIf (b : bexp) (c₁ c₂ : com)
| CWhile (b : bexp) (c : com)
| CRepeat (c : com) (b : bexp)

open com

/-
Notation "'SKIP'" :=
  CSkip.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state → com → state → Prop :=
  | E_Skip : ∀st,
      ceval st SKIP st
  | E_Ass : ∀st a1 n X,
      aeval st a1 = n →
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : ∀c1 c2 st st' st'',
      ceval st c1 st' →
      ceval st' c2 st'' →
      ceval st (c1 ; c2) st''
  | E_IfTrue : ∀st st' b1 c1 c2,
      beval st b1 = true →
      ceval st c1 st' →
      ceval st (TEST b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : ∀st st' b1 c1 c2,
      beval st b1 = false →
      ceval st c2 st' →
      ceval st (TEST b1 THEN c1 ELSE c2 FI) st'
  | E_WhileFalse : ∀b1 st c1,
      beval st b1 = false →
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileTrue : ∀st st' st'' b1 c1,
      beval st b1 = true →
      ceval st c1 st' →
      ceval st' (WHILE b1 DO c1 END) st'' →
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : ∀st st' b1 c1,
      ceval st c1 st' →
      beval st' b1 = true →
      ceval st (CRepeat c1 b1) st'
  | E_RepeatLoop : ∀st st' st'' b1 c1,
      ceval st c1 st' →
      beval st' b1 = false →
      ceval st' (CRepeat c1 b1) st'' →
      ceval st (CRepeat c1 b1) st''.

Notation "st '=[' c ']⇒' st'" := (ceval st c st')
                                 (at level 40).
-/

local notation `SKIP` := CSkip
local infix ` ::= `:60 := CAsgn
local infix ` ;; `:35 := CSeq
local notation `WHILE ` b ` DO ` c ` END` := CWhile b c
local notation `TEST ` c₁ ` THEN ` c₂ ` ELSE ` c₃ ` FI` := CIf c₁ c₂ c₃
local notation `REPEAT ` e₁ ` UNTIL ` b₂ ` END` := CRepeat e₁ b₂

inductive ceval : com → imp.state → imp.state → Prop
| E_Skip : ∀st, ceval SKIP st st
| E_Ass : ∀{st a₁ n} x,
  aeval st a₁ = n →
  ceval (x ::= a₁) st (x !→ n ; st)
| E_Seq : ∀{c₁ c₂ st st' st''},
  ceval c₁ st st' →
  ceval c₂ st' st'' →
  ceval (c₁ ;; c₂) st st''
| E_IfTrue : ∀{st st' b c₁} c₂,
  beval st b = tt →
  ceval c₁ st st' →
  ceval (TEST b THEN c₁ ELSE c₂ FI) st st'
| E_IfFalse : ∀{st st' b} c₁ {c₂},
  beval st b = ff →
  ceval c₂ st st' →
  ceval (TEST b THEN c₁ ELSE c₂ FI) st st'
| E_WhileFalse : ∀{b st} c,
  beval st b = ff →
  ceval (WHILE b DO c END) st st
| E_WhileTrue : ∀{st st' st'' b c},
  beval st b = tt →
  ceval c st st' →
  ceval (WHILE b DO c END) st' st'' →
  ceval (WHILE b DO c END) st st''
| E_RepeatEnd : ∀{st st' b c},
  ceval c st st' →
  beval st' b = tt →
  ceval (REPEAT c UNTIL b END) st st'
| E_RepeatLoop : ∀{st st' st'' b c},
  ceval c st st' →
  beval st' b = ff →
  ceval (REPEAT c UNTIL b END) st' st'' →
  ceval (REPEAT c UNTIL b END) st st''

open ceval

local notation st ` =[ ` c ` ]⇒ ` st' := ceval c st st'

open imp

/-
Theorem ceval_deterministic: ∀c st st1 st2,
    st =[ c ]⇒ st1 →
    st =[ c ]⇒ st2 →
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwinv.
       (* oops: why didn't find_rwinv solve this for us already?
          answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwinv.
Qed.
-/

/-
TODO: for reasons i cannot even begin to fathom,
using notation for h₂ breaks it

note: ifinish can handle find_rwinv so moving find_eqn makes no difference
-/
theorem ceval_deterministic {c : com} {st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : ceval c st st₂)
  : st₁ = st₂ :=
begin
  induction h₁ generalizing st₂;
    inv h₂;
    try { refl <|> find_rwinv };
    find_eqn;
    ifinish,
end

/-
Theorem ceval_deterministic': ∀c st st1 st2,
    st =[ c ]⇒ st1 →
    st =[ c ]⇒ st2 →
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inv E2; repeat find_eqn; try find_rwinv; auto.
Qed.
End Repeat.
-/

theorem ceval_deterministic' {c : com} {st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : ceval c st st₂)
  : st₁ = st₂ :=
begin
  induction h₁ generalizing st₂;
    inv h₂;
    find_eqn;
    try { refl <|> find_rwinv };
    ifinish,
end

end repeat

/-
Example ceval_example1:
  empty_st =[
    X ::= 2;;
    TEST X ≤ 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]⇒ (Z !-> 4 ; X !-> 2).
Proof.
  (* We supply the intermediate state st'... *)
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.
-/

example :
  empty_st =[
    X ::= 2;;
    TEST X ≤' 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]⇒ Z !→ 4 ; X !→ 2 :=
begin
  apply E_Seq,
    apply E_Ass,
    refl,
  apply E_IfFalse,
    refl,
  apply E_Ass,
  refl,
end

/-
Example ceval'_example1:
  empty_st =[
    X ::= 2;;
    TEST X ≤ 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]⇒ (Z !-> 4 ; X !-> 2).
Proof.
  eapply E_Seq. (* 1 *)
  - apply E_Ass. (* 2 *)
    reflexivity. (* 3 *)
  - (* 4 *) apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.
-/

/-
eapply doesn't create the metavariable subgoal,
but it doesn't have any other noticeable effects in this proof
-/

example :
  empty_st =[
    X ::= 2;;
    TEST X ≤' 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]⇒ Z !→ 4 ; X !→ 2 :=
begin
  eapply E_Seq,
    eapply E_Ass,
    refl,
  eapply E_IfFalse,
    refl,
  eapply E_Ass,
  refl,
end

/-
Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Definition st12 := (Y !-> 2 ; X !-> 1).
Definition st21 := (Y !-> 1 ; X !-> 2).

Example eauto_example : ∃s',
  st21 =[
    TEST X ≤ Y
      THEN Z ::= Y - X
      ELSE Y ::= X + Z
    FI
  ]⇒ s'.
Proof. eauto. Qed.
-/

/-
TODO: no finishing tactic handles this
-/

-- def st₁₂ := Y !→ 2 ; X !→ 1
-- def st₂₁ := Y !→ 1 ; X !→ 2

-- example : ∃s',
--   st₂₁ =[
--     TEST X ≤' Y
--       THEN Z ::= Y - X
--       ELSE Y ::= X + Z
--     FI
--   ]⇒ s' := by ifinish
