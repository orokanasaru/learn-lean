import
  tactic.basic
  tactic.omega
  .ch08_maps

open
  basics (eqb leb)
  logic (In)
  maps (total_map t_empty t_update)

local infix ` =? `:50 := eqb
local infix ` ≤? `:50 := leb
local notation `__` ` !→ `:10 v := t_empty v
local notation x ` !→ `:10 v:5 ` ; ` m := t_update m x v

variables {P : Prop}
          {m n o p : ℕ}

namespace imp.aeval_basic

/-
  Inductive aexp : Type :=
    | ANum (n : nat)
    | APlus (a1 a2 : aexp)
    | AMinus (a1 a2 : aexp)
    | AMult (a1 a2 : aexp).

  Inductive bexp : Type :=
    | BTrue
    | BFalse
    | BEq (a1 a2 : aexp)
    | BLe (a1 a2 : aexp)
    | BNot (b : bexp)
    | BAnd (b1 b2 : bexp).
-/

inductive aexp : Type
  | ANum (n : ℕ)
  | APlus (a₁ a₂ : aexp)
  | AMinus (a₁ a₂ : aexp)
  | AMult (a₁ a₂ : aexp)

inductive bexp : Type
  | BTrue
  | BFalse
  | BEq (a₁ a₂ : aexp)
  | BLe (a₁ a₂ : aexp)
  | BNot (b : bexp)
  | BAnd (b₁ b₂ : bexp)

open aexp bexp

variables {a a₁ a₂ : aexp} {b b₁ b₂ : bexp}

/-
  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n ⇒ n
    | APlus a1 a2 ⇒ (aeval a1) + (aeval a2)
    | AMinus a1 a2 ⇒ (aeval a1) - (aeval a2)
    | AMult a1 a2 ⇒ (aeval a1) * (aeval a2)
    end.

  Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. reflexivity. Qed.
-/

def aeval : aexp → ℕ
  | (ANum n) := n
  | (APlus a₁ a₂) := aeval a₁ + aeval a₂
  | (AMinus a₁ a₂) := aeval a₁ - aeval a₂
  | (AMult a₁ a₂) := aeval a₁ * aeval a₂

example : aeval (APlus (ANum 2) (ANum 2)) = 4 := rfl

/-
  Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue ⇒ true
  | BFalse ⇒ false
  | BEq a1 a2 ⇒ (aeval a1) =? (aeval a2)
  | BLe a1 a2 ⇒ (aeval a1) <=? (aeval a2)
  | BNot b1 ⇒ negb (beval b1)
  | BAnd b1 b2 ⇒ andb (beval b1) (beval b2)
  end.
-/

def beval : bexp → bool
  | BTrue := tt
  | BFalse := ff
  | (BEq a₁ a₂) := aeval a₁ =? aeval a₂
  | (BLe a₁ a₂) := aeval a₁ ≤? aeval a₂
  | (BNot b₁) := bnot (beval b₁)
  | (BAnd b₁ b₂) := band (beval b₁) (beval b₂)

/-
  Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n ⇒ ANum n
  | APlus (ANum 0) e2 ⇒ optimize_0plus e2
  | APlus e1 e2 ⇒ APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 ⇒ AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 ⇒ AMult (optimize_0plus e1) (optimize_0plus e2)
  end.
-/

def optimize_0plus : aexp → aexp
  | (ANum n) := (ANum n)
  | (APlus (ANum 0) e₂) := optimize_0plus e₂
  | (APlus e₁ e₂) := APlus (optimize_0plus e₁) (optimize_0plus e₂)
  | (AMinus e₁ e₂) := AMinus (optimize_0plus e₁) (optimize_0plus e₂)
  | (AMult e₁ e₂) := AMult (optimize_0plus e₁) (optimize_0plus e₂)

/-
  Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. reflexivity. Qed.
-/

example :
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1) := rfl

/-
  Theorem optimize_0plus_sound: ∀a,
    aeval (optimize_0plus a) = aeval a.
  Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.
-/

theorem optimize_0plus_sound : aeval (optimize_0plus a) = aeval a :=
begin
  induction a,
  case ANum { refl, },
  case APlus : a₁ a₂ ih₁ ih₂ {
    cases a₁,
    case ANum : n {
      cases n,
        unfold optimize_0plus aeval,
        rw zero_add,
        exact ih₂,
      unfold optimize_0plus aeval,
      rw ih₂,
    },
    case APlus : a₁' a₂' {
      unfold optimize_0plus aeval,
      unfold aeval at ih₁,
      rw [ih₁, ih₂],
    },
    case AMinus : a₁' a₂' {
      unfold optimize_0plus aeval at ih₁ ⊢,
      rw [ih₁, ih₂],
    },
    case AMult : a₁' a₂' {
      unfold optimize_0plus aeval at ih₁ ⊢,
      rw [ih₁, ih₂],
    },
  },
  case AMinus : a₁ a₂ ih₁ ih₂ {
    unfold optimize_0plus aeval,
    rw [ih₁, ih₂],
  },
  case AMult : a₁ a₂ ih₁ ih₂ {
    unfold optimize_0plus aeval,
    rw [ih₁, ih₂],
  },
end

/-
  Theorem silly1 : ∀ae, aeval ae = aeval ae.
  Proof. try reflexivity. (* This just does reflexivity. *) Qed.

  Theorem silly2 : ∀(P : Prop), P → P.
  Proof.
    intros P HP.
    try reflexivity. (* Just reflexivity would have failed. *)
    apply HP. (* We can still finish the proof in some other way. *)
  Qed.
-/

theorem silly₁ : aeval a = aeval a := by try { reflexivity, }

theorem silly₂ (hp : P) : P :=
begin
  try { reflexivity, },
  exact hp,
end

/-
  Lemma foo : ∀n, 0 <=? n = true.
  Proof.
    intros.
    destruct n.
      (* Leaves two subgoals, which are discharged identically...  *)
      - (* n=0 *) simpl. reflexivity.
      - (* n=Sn' *) simpl. reflexivity.
  Qed.
-/

lemma foo : 0 ≤ n = tt :=
begin
  cases n,
    rw le_zero_iff_eq,
    simp only [bool.coe_sort_tt, eq_self_iff_true],
  simp only [bool.coe_sort_tt, zero_le],
end

/-
  Lemma foo' : ∀n, 0 <=? n = true.
  Proof.
    intros.
    (* destruct the current goal *)
    destruct n;
    (* then simpl each resulting subgoal *)
    simpl;
    (* and do reflexivity on each resulting subgoal *)
    reflexivity.
  Qed.
-/

lemma foo' : 0 ≤ n = tt :=
by cases n; simp only [
  le_zero_iff_eq, bool.coe_sort_tt, eq_self_iff_true, bool.coe_sort_tt, zero_le
]

/-
  Theorem optimize_0plus_sound': ∀a,
    aeval (optimize_0plus a) = aeval a.
  Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the try...
       does nothing, is when e1 = ANum n. In this
       case, we have to destruct n (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity. Qed.
-/

theorem optimize_0plus_sound' : aeval (optimize_0plus a) = aeval a :=
begin
  induction a with n a₁ a₂ ih₁ ih₂ a₁ a₂ ih₁ ih₂ a₁ a₂ ih₁ ih₂; try {
    unfold optimize_0plus aeval,
    rw [ih₁, ih₂],
  },
  case ANum { refl, },
  case APlus {
    cases a₁; try {
      unfold optimize_0plus aeval at ih₁ ⊢,
      rw [ih₁, ih₂],
    },
    case ANum : n {
      cases n; unfold optimize_0plus aeval; try { rw zero_add, }; rw ih₂,
    },
  },
end

/-
  Theorem optimize_0plus_sound'': ∀a,
    aeval (optimize_0plus a) = aeval a.
  Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.
-/

theorem optimize_0plus_sound'' : aeval (optimize_0plus a) = aeval a :=
begin
  induction a; try {
    unfold optimize_0plus aeval,
    simp only *,
  }; try { refl, },
  case APlus : a₁ a₂ ih₁ ih₂ {
    cases a₁; try {
      unfold optimize_0plus aeval at ih₁ ⊢,
      rw [ih₁, ih₂],
    },
    case ANum : n {
      cases n; unfold optimize_0plus aeval; try { rw zero_add, }; rw ih₂,
    },
  },
end

/-
  Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.
-/

theorem In₁₀ : In 10 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :=
by repeat { try { left; refl, }; right, }

/-
  Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (left; reflexivity).
    repeat (right; try (left; reflexivity)).
  Qed.
-/

theorem In₁₀' : In 10 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :=
begin
  repeat {left; refl},
  repeat {right; try { left; refl }},
end

theorem In₁₀'' : In 10 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :=
by repeat { { left; refl, } <|> right, }

/-
  Fixpoint optimize_0plus_b (b : bexp) : bexp
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Theorem optimize_0plus_b_sound : ∀b,
    beval (optimize_0plus_b b) = beval b.
  Proof.
  (* FILL IN HERE *) Admitted.
-/

def optimize_0plus_b : bexp → bexp
  | BTrue := BTrue
  | BFalse := BFalse
  | (BEq a₁ a₂) := BEq (optimize_0plus a₁) (optimize_0plus a₂)
  | (BLe a₁ a₂) := BLe (optimize_0plus a₁) (optimize_0plus a₂)
  | (BNot b) := BNot (optimize_0plus_b b)
  | (BAnd b₁ b₂) := BAnd (optimize_0plus_b b₁) (optimize_0plus_b b₂)

theorem optimize_0plus_b_sound : beval (optimize_0plus_b b) = beval b :=
begin
  induction b;
  simp only [
    optimize_0plus_b, beval, *, bool.to_bool_eq, optimize_0plus_sound
  ],
end

/-
  Tactic Notation "simpl_and_try" tactic(c) :=
    simpl;
    try c.
-/

end imp.aeval_basic

/-
  TODO: is there a way to write to root namespace directly?
-/
namespace tactic

meta def simpl_and_try {α : Type} (c : tactic α) : tactic unit := do
  s ← simp_lemmas.mk_default,
  /- unlike coq, lean's simp can fail -/
  try $ simp_target s,
  try c

end tactic

namespace tactic.interactive

meta def simpl_and_try (c : itactic) : tactic unit := tactic.simpl_and_try c

end tactic.interactive

namespace imp
namespace aeval_basic

open aexp bexp

variables {a a₁ a₂ : aexp} {b b₁ b₂ : bexp}

/-
  Example silly_presburger_example : ∀m n o p,
    m + n ≤ n + o ∧ o + 3 = p + 3 →
    m ≤ p.
  Proof.
    intros. omega.
  Qed.
-/

lemma omega_test (h : m + n ≤ n + o ∧ o + 3 = p + 3) : m ≤ p :=
begin
  cases h with hl hr,
  have : o = p, injections,
  rw ←this,
  rw add_comm n at hl,
  rwa nat.add_le_add_iff_le_right at hl,
end

#print omega_test
#print axioms omega_test

lemma omega_test' (h : m + n ≤ n + o ∧ o + 3 = p + 3) : m ≤ p := by omega

#print omega_test'

/-
  TODO: why does omega require classical.choice?
-/
#print axioms omega_test'

/-
  Module aevalR_first_try.

  Inductive aevalR : aexp → nat → Prop :=
    | E_ANum n :
        aevalR (ANum n) n
    | E_APlus (e1 e2: aexp) (n1 n2: nat) :
        aevalR e1 n1 →
        aevalR e2 n2 →
        aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
        aevalR e1 n1 →
        aevalR e2 n2 →
        aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult (e1 e2: aexp) (n1 n2: nat) :
        aevalR e1 n1 →
        aevalR e2 n2 →
        aevalR (AMult e1 e2) (n1 * n2).

  Module TooHardToRead.

  (* A small notational aside. We would previously have written the
    definition of aevalR like this, with explicit names for the
    hypotheses in each case: *)
  Inductive aevalR : aexp → nat → Prop :=
    | E_ANum n :
        aevalR (ANum n) n
    | E_APlus (e1 e2: aexp) (n1 n2: nat)
        (H1 : aevalR e1 n1)
        (H2 : aevalR e2 n2) :
        aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2: aexp) (n1 n2: nat)
        (H1 : aevalR e1 n1)
        (H2 : aevalR e2 n2) :
        aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult (e1 e2: aexp) (n1 n2: nat)
        (H1 : aevalR e1 n1)
        (H2 : aevalR e2 n2) :
        aevalR (AMult e1 e2) (n1 * n2).

  End TooHardToRead.
-/

namespace aevalR_first_try

inductive aevalR : aexp → ℕ → Prop
  | E_ANum (n) : aevalR (ANum n) n
  | E_APlus (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (APlus e₁ e₂) (n₁ + n₂)
  | E_AMinus (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMinus e₁ e₂) (n₁ - n₂)
  | E_AMult (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMult e₁ e₂) (n₁ * n₂)

namespace too_hard_to_read

inductive aevalR : aexp → ℕ → Prop
  | E_ANum (n) : aevalR (ANum n) n
  | E_APlus {e₁ e₂ n₁ n₂} (h₁ : aevalR e₁ n₁) (h₂ : aevalR e₂ n₂)
    : aevalR (APlus e₁ e₂) (n₁ + n₂)
  | E_AMinus {e₁ e₂ n₁ n₂} (h₁ : aevalR e₁ n₁) (h₂ : aevalR e₂ n₂)
    : aevalR (AMinus e₁ e₂) (n₁ - n₂)
  | E_AMult {e₁ e₂ n₁ n₂} (h₁ : aevalR e₁ n₁) (h₂ : aevalR e₂ n₂)
    : aevalR (AMult e₁ e₂) (n₁ * n₂)

end too_hard_to_read

/-
  Notation "e '\\' n"
          := (aevalR e n)
              (at level 50, left associativity)
          : type_scope.

  End aevalR_first_try.
-/

local infixl ` \\ `:65 := aevalR

end aevalR_first_try

/-
  Reserved Notation "e '\\' n" (at level 90, left associativity).
  Inductive aevalR : aexp → nat → Prop :=
    | E_ANum (n : nat) :
        (ANum n) \\ n
    | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
        (e1 \\ n1) → (e2 \\ n2) → (APlus e1 e2) \\ (n1 + n2)
    | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
        (e1 \\ n1) → (e2 \\ n2) → (AMinus e1 e2) \\ (n1 - n2)
    | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
        (e1 \\ n1) → (e2 \\ n2) → (AMult e1 e2) \\ (n1 * n2)

    where "e '\\' n" := (aevalR e n) : type_scope.
-/

/-
  TODO: no idea why level changes in the sf book
-/
reserve infixl ` \\ `:25

/-
  TODO: i don't see a way to use reserved notation in a lean definition
-/
inductive aevalR : aexp → ℕ → Prop
  | E_ANum (n) : aevalR (ANum n) n
  | E_APlus {e₁ e₂ n₁ n₂} :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (APlus e₁ e₂) (n₁ + n₂)
  | E_AMinus {e₁ e₂ n₁ n₂} :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMinus e₁ e₂) (n₁ - n₂)
  | E_AMult {e₁ e₂ n₁ n₂} :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMult e₁ e₂) (n₁ * n₂)

open aevalR

infixl ` \\ ` :=  aevalR

/-
  Theorem aeval_iff_aevalR : ∀a n,
    (a \\ n) ↔ aeval a = n.
  Proof.
  split.
  - (* -> *)
    intros H.
    induction H; simpl.
    + (* E_ANum *)
      reflexivity.
    + (* E_APlus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMinus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMult *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a;
        simpl; intros; subst.
    + (* ANum *)
      apply E_ANum.
    + (* APlus *)
      apply E_APlus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
    + (* AMinus *)
      apply E_AMinus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
    + (* AMult *)
      apply E_AMult.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
  Qed.
-/

/-
  TODO: maybe fix unfold/subst so they propagate tags
-/
theorem aeval_iff_aevalR : a \\ n ↔ aeval a = n :=
begin
  split,
    intro h,
    induction h; simp only [aeval],
    case E_APlus : e₁ e₂ n₁ n₂ h₁ h₂ ih₁ ih₂ { rw [ih₁, ih₂], },
    case E_AMinus : e₁ e₂ n₁ n₂ h₁ h₂ ih₁ ih₂ { rw [ih₁, ih₂], },
    case E_AMult : e₁ e₂ n₁ n₂ h₁ h₂ ih₁ ih₂ { rw [ih₁, ih₂], },
  intro h,
  induction a generalizing n; simp only [←h] at *,
  case ANum { apply E_ANum, },
  case APlus : a₁ a₂ ih₁ ih₂ {
    apply E_APlus,
      apply ih₁,
      refl,
    apply ih₂,
    refl,
  },
  case AMinus : a₁ a₂ ih₁ ih₂ {
    apply E_AMinus,
      apply ih₁,
      refl,
    apply ih₂,
    refl,
  },
  case AMult : a₁ a₂ ih₁ ih₂ {
    apply E_AMult,
      apply ih₁,
      refl,
    apply ih₂,
    refl,
  },
end

/-
  Theorem aeval_iff_aevalR' : ∀a n,
    (a \\ n) ↔ aeval a = n.
  Proof.
    (* WORKED IN CLASS *)
    split.
    - (* -> *)
      intros H; induction H; subst; reflexivity.
    - (* <- *)
      generalize dependent n.
      induction a; simpl; intros; subst; constructor;
        try apply IHa1; try apply IHa2; reflexivity.
  Qed.
-/

theorem aeval_iff_aevalR' : a \\ n ↔ aeval a = n :=
begin
  split,
    intro h; induction h; unfold aeval; subst_vars,
  intro h; induction a generalizing n; subst h; constructor;
    apply a_ih_a₁ <|> apply a_ih_a₂; refl,
end

/-
  Inductive bevalR: bexp → bool → Prop :=
  (* FILL IN HERE *)
  .

  Lemma beval_iff_bevalR : ∀b bv,
    bevalR b bv ↔ beval b = bv.
  Proof.
  (* FILL IN HERE *) Admitted.
-/

inductive bevalR : bexp → bool → Prop
  | E_BTrue : bevalR BTrue tt
  | E_BFalse : bevalR BFalse ff
  | E_BEq (e₁ e₂ n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → bevalR (BEq e₁ e₂) (n₁ = n₂)
  | E_BLe (e₁ e₂ n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → bevalR (BLe e₁ e₂) (n₁ ≤ n₂)
  | E_BNot (e₁ b₁) : bevalR e₁ b₁ → bevalR (BNot e₁) (¬b₁)
  | E_BAnd (e₁ e₂ b₁ b₂) :
    bevalR e₁ b₁ → bevalR e₂ b₂ → bevalR (BAnd e₁ e₂) (b₁ && b₂)

open bevalR

lemma reflect_imp_em {bv : bool} (h : indprop.reflect P bv) : P ∨ ¬P :=
begin
  cases h with h' h',
    exact or.inl h',
  exact or.inr h',
end

lemma eqb_iff_eq : n =? m = (n = m) :=
begin
  cases reflect_imp_em (@indprop.eqbP n m),
    suggest,
end


#check decidable

lemma beval_iff_bevalR {bv} : bevalR b bv ↔ beval b = bv :=
begin
  split,
    intro h,
    induction h,
    case E_BTrue { unfold beval, },
    case E_BFalse { unfold beval, },
    case E_BEq : e₁ e₂ n₁ n₂ a₁ a₂ {
      unfold beval,
      rw aeval_iff_aevalR at *,
      rw [a₁, a₂],
      exact eqb_iff_eq,
    },
    case E_BLe : e₁ e₂ n₁ n₂ a₁ a₂ {
      unfold beval,
      rw aeval_iff_aevalR at *,
      rw [a₁, a₂],
    },
    case E_BNot : e₁ b₁ a ih {
      unfold beval,
      rw ih,
    },
    case E_BAnd : e₁ e₂ b₁ b₂ a₁ a₂ ih₁ ih₂ {
      unfold beval,
      rw [ih₁, ih₂],
    },
  intro h,
  induction b generalizing bv,
  case BTrue {
    subst h,
    unfold beval,
    constructor,
  },
  case BFalse {
    subst h,
    unfold beval,
    constructor,
  },
  case BEq : a₁ a₂ {
    subst h,
    unfold beval,
    constructor,
      rw aeval_iff_aevalR,
    rw aeval_iff_aevalR,
  },
  case BLe : a₁ a₂ {
    subst h,
    unfold beval,
    constructor,
      rw aeval_iff_aevalR,
    rw aeval_iff_aevalR,
  },
  case BNot : b ih {
    subst h,
    unfold beval,
    constructor,
    apply ih,
    refl,
  },
  case BAnd : b₁ b₂ ih₁ ih₂ {
    subst h,
    unfold beval,
    constructor,
      apply ih₁,
      refl,
    apply ih₂,
    refl,
  }
end

lemma beval_iff_bevalR' {bv} : bevalR b bv ↔ beval b = bv :=
begin
  split; intro h,
    induction h; simp only [aeval_iff_aevalR, beval, bool.to_bool_eq, *] at *,
  induction b generalizing bv; subst h; constructor;
    simp only [aeval_iff_aevalR, *],
end

end aeval_basic

/-
  Module aevalR_division.
-/

namespace aevalR_division

/-
  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <--- NEW *)
-/

inductive aexp : Type
  | ANum (n : ℕ)
  | APlus (a₁ a₂ : aexp)
  | AMinus (a₁ a₂ : aexp)
  | AMult (a₁ a₂ : aexp)
  | ADiv (a₁ a₂ : aexp) /- new -/

open aexp

/-
  Reserved Notation "e '\\' n"
                    (at level 90, left associativity).

  Inductive aevalR : aexp → nat → Prop :=
    | E_ANum (n : nat) :
        (ANum n) \\ n
    | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) → (a2 \\ n2) → (APlus a1 a2) \\ (n1 + n2)
    | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) → (a2 \\ n2) → (AMinus a1 a2) \\ (n1 - n2)
    | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) → (a2 \\ n2) → (AMult a1 a2) \\ (n1 * n2)
    | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
        (a1 \\ n1) → (a2 \\ n2) → (n2 > 0) →
        (mult n2 n3 = n1) → (ADiv a1 a2) \\ n3

  where "a '\\' n" := (aevalR a n) : type_scope.

  End aevalR_division.

  Module aevalR_extended.
-/

inductive aevalR : aexp → ℕ → Prop
  | E_ANum (n) : aevalR (ANum n) n
  | E_APlus (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (APlus e₁ e₂) (n₁ + n₂)
  | E_AMinus (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMinus e₁ e₂) (n₁ - n₂)
  | E_AMult (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMult e₁ e₂) (n₁ * n₂)
  | E_ADiv (e₁ e₂) (n₁ n₂ n₃) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → n₂ > 0 → n₂ * n₃ = n₁ → aevalR (ADiv e₁ e₂) n₃

end aevalR_division

namespace aevalR_extended

/-
  Reserved Notation "e '\\' n" (at level 90, left associativity).

  Inductive aexp : Type :=
    | AAny (* <--- NEW *)
    | ANum (n : nat)
    | APlus (a1 a2 : aexp)
    | AMinus (a1 a2 : aexp)
    | AMult (a1 a2 : aexp).
-/

inductive aexp : Type
  | AAny
  | ANum (n : ℕ)
  | APlus (a₁ a₂ : aexp)
  | AMinus (a₁ a₂ : aexp)
  | AMult (a₁ a₂ : aexp)

open aexp

/-
  Inductive aevalR : aexp → nat → Prop :=
    | E_Any (n : nat) :
        AAny \\ n (* <--- NEW *)
    | E_ANum (n : nat) :
        (ANum n) \\ n
    | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) → (a2 \\ n2) → (APlus a1 a2) \\ (n1 + n2)
    | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) → (a2 \\ n2) → (AMinus a1 a2) \\ (n1 - n2)
    | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) → (a2 \\ n2) → (AMult a1 a2) \\ (n1 * n2)

  where "a '\\' n" := (aevalR a n) : type_scope.

  End aevalR_extended.
-/

inductive aevalR : aexp → ℕ → Prop
  | E_AAny (n) : aevalR AAny n
  | E_ANum (n) : aevalR (ANum n) n
  | E_APlus (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (APlus e₁ e₂) (n₁ + n₂)
  | E_AMinus (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMinus e₁ e₂) (n₁ - n₂)
  | E_AMult (e₁ e₂) (n₁ n₂) :
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMult e₁ e₂) (n₁ * n₂)

end aevalR_extended

/-
  Definition state := total_map nat.
-/

def state := total_map ℕ

/-
  Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
-/

inductive aexp : Type
  | ANum (n : ℕ)
  | AId (x : string)
  | APlus (a₁ a₂ : aexp)
  | AMinus (a₁ a₂ : aexp)
  | AMult (a₁ a₂ : aexp)

open aexp

/-
  Definition W : string := "W".
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z".
-/

def W := "W"
def X := "X"
def Y := "Y"
def Z := "Z"

/-
  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
-/

inductive bexp : Type
  | BTrue
  | BFalse
  | BEq (a₁ a₂ : aexp)
  | BLe (a₁ a₂ : aexp)
  | BNot (b : bexp)
  | BAnd (b₁ b₂ : bexp)

open bexp

/-
  Coercion AId : string >-> aexp.
  Coercion ANum : nat >-> aexp.

  Definition bool_to_bexp (b : bool) : bexp :=
    if b then BTrue else BFalse.
  Coercion bool_to_bexp : bool >-> bexp.

  Bind Scope imp_scope with aexp.
  Bind Scope imp_scope with bexp.
  Delimit Scope imp_scope with imp.

  Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
  Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
  Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
  Notation "x ≤ y" := (BLe x y) (at level 70, no associativity) : imp_scope.
  Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
  Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
  Notation "'¬' b" := (BNot b) (at level 75, right associativity) : imp_scope.

  Definition example_aexp := (3 + (X * 2))%imp : aexp.
  Definition example_bexp := (true && ~(X ≤ 4))%imp : bexp.
-/

instance string_to_aexp : has_coe string aexp := ⟨AId⟩
instance nat_to_aexp : has_coe ℕ aexp := ⟨ANum⟩

instance bool_to_bexp : has_coe bool bexp :=
  ⟨λb, if b then BTrue else BFalse⟩

/-
  TODO: for whatever reason, need zero, one, and add instances
  using instances instead of notation for all aexp stuff
-/
instance aexp_zero : has_zero aexp := ⟨ANum 0⟩
instance aexp_one : has_one aexp := ⟨ANum 1⟩
instance aexp_add : has_add aexp := ⟨APlus⟩
instance aexp_sub : has_sub aexp := ⟨AMinus⟩
instance aexp_mul : has_mul aexp := ⟨AMult⟩

local infix ≤ := BLe

/-
  TODO: don't use notation on =
  it breaks generalize and requires type annotation everywhere else
-/
local infix == := BEq
local infixl && := BAnd
local notation ¬b := BNot b

def example_aexp : aexp := 3 + (X * 2)
def example_bexp := tt && ¬(X ≤ 4)

/-
  Set Printing Coercions.

  Print example_bexp.
  (* ===> example_bexp = bool_to_bexp true && ~ (AId X <= ANum 4) *)

  Unset Printing Coercions.
-/

/-
  TODO: true by default. seems much less useful than in coq
-/

set_option pp.coercions true

#print example_bexp

/-
  Fixpoint aeval (st : state) (a : aexp) : nat :=
    match a with
    | ANum n ⇒ n
    | AId x ⇒ st x (* <--- NEW *)
    | APlus a1 a2 ⇒ (aeval st a1) + (aeval st a2)
    | AMinus a1 a2 ⇒ (aeval st a1) - (aeval st a2)
    | AMult a1 a2 ⇒ (aeval st a1) * (aeval st a2)
    end.

  Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue ⇒ true
  | BFalse ⇒ false
  | BEq a1 a2 ⇒ (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 ⇒ (aeval st a1) <=? (aeval st a2)
  | BNot b1 ⇒ negb (beval st b1)
  | BAnd b1 b2 ⇒ andb (beval st b1) (beval st b2)
  end.
-/

def aeval (st : state) : aexp → ℕ
  | (ANum n) := n
  | (AId x) := st x /- new -/
  | (APlus a₁ a₂) := aeval a₁ + aeval a₂
  | (AMinus a₁ a₂) := aeval a₁ - aeval a₂
  | (AMult a₁ a₂) := aeval a₁ * aeval a₂

def beval (st : state): bexp → bool
  | BTrue := tt
  | BFalse := ff
  | (BEq a₁ a₂) := aeval st a₁ = aeval st a₂
  | (BLe a₁ a₂) := aeval st a₁ ≤? aeval st a₂
  | (BNot b₁) := bnot (beval b₁)
  | (BAnd b₁ b₂) := band (beval b₁) (beval b₂)

/-
  Definition empty_st := (_ !-> 0).
-/

def empty_st := __ !→ 0

/-
  Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

  Example aexp1 :
      aeval (X !-> 5) (3 + (X * 2))%imp
    = 13.
  Proof. reflexivity. Qed.

  Example bexp1 :
      beval (X !-> 5) (true && ~(X ≤ 4))%imp
    = true.
  Proof. reflexivity. Qed.
-/

local notation x ` !→ `:10 v := t_update empty_st x v

example : aeval (X !→ 5) (3 + (X * 2)) = 13 := rfl

example : beval (X !→ 5) (tt && ¬(X ≤ 4)) = tt := rfl

/-
  Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
-/

inductive com
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c₁ c₂ : com)
  | CIf (b : bexp) (c₁ c₂ : com)
  | CWhile (b : bexp) (c : com)

open com

/-
  Bind Scope imp_scope with com.
  Notation "'SKIP'" :=
    CSkip : imp_scope.
  Notation "x '::=' a" :=
    (CAss x a) (at level 60) : imp_scope.
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity) : imp_scope.
  Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.
-/

local notation `SKIP` := CSkip
local infix ` ::= `:60 := CAss
local infix ` ;; `:35 := CSeq
local notation `WHILE ` b ` DO ` c ` END` := CWhile b c
local notation `TEST ` c₁ ` THEN ` c₂ ` ELSE ` c₃ ` FI` := CIf c₁ c₂ c₃

/-
  Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.
-/

def fact_in_lean : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ¬(Z == 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END

/-
  Unset Printing Notations.
  Print fact_in_coq.
  (* ===>
    fact_in_coq =
    CSeq (CAss Z X)
          (CSeq (CAss Y (S O))
                (CWhile (BNot (BEq Z O))
                        (CSeq (CAss Y (AMult Y Z))
                              (CAss Z (AMinus Z (S O))))))
          : com *)
  Set Printing Notations.

  Set Printing Coercions.
  Print fact_in_coq.
  (* ===>
    fact_in_coq =
    (Z ::= AId X;;
    Y ::= ANum 1;;
    WHILE ~ (AId Z = ANum 0) DO
      Y ::= AId Y * AId Z;;
      Z ::= AId Z - ANum 1
    END)%imp
        : com *)
  Unset Printing Coercions.
-/

set_option pp.notation false
#print fact_in_lean
set_option pp.notation true

#print fact_in_lean

/-
  Locate "&&".
  (* ===>
    Notation "x && y" := andb x y : bool_scope (default interpretation) *)

  Locate ";;".
  (* ===>
    Notation "c1 ;; c2" := CSeq c1 c2 : imp_scope (default interpretation) *)

  Locate "WHILE".
  (* ===>
    Notation "'WHILE' b 'DO' c 'END'" := CWhile b c : imp_scope
    (default interpretation) *)
-/

#print &&
#print ;;
#print WHILE
#print notation WHILE

/-
  Locate aexp.
  (* ===>
    Inductive Top.aexp
    Inductive Top.AExp.aexp
      (shorter name to refer to it in current context is AExp.aexp)
    Inductive Top.aevalR_division.aexp
      (shorter name to refer to it in current context is aevalR_division.aexp)
    Inductive Top.aevalR_extended.aexp
      (shorter name to refer to it in current context is aevalR_extended.aexp)
  *)
-/

#print aexp
#print inductive aexp

/-
  Definition plus2 : com :=
    X ::= X + 2.

  Definition XtimesYinZ : com :=
    Z ::= X * Y.

  Definition subtract_slowly_body : com :=
    Z ::= Z - 1 ;;
    X ::= X - 1.
-/

def plus₂ : com := X ::= X + 2

def XtimesYinZ : com := Z ::= X * Y

def subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1

/-
  Definition subtract_slowly : com :=
    (WHILE ~(X = 0) DO
      subtract_slowly_body
    END)%imp.

  Definition subtract_3_from_5_slowly : com :=
    X ::= 3 ;;
    Z ::= 5 ;;
    subtract_slowly.
-/

def subtract_slowly : com :=
  WHILE ¬X == 0 DO
    subtract_slowly_body
  END

def subtract_3_from_5_slowly : com :=
  X ::= 3;;
  Z ::= 5;;
  subtract_slowly

/-
  Definition loop : com :=
    WHILE true DO
      SKIP
    END.
-/

def loop : com :=
  WHILE tt DO
    SKIP
  END

/-
  Open Scope imp_scope.
  Fixpoint ceval_fun_no_while (st : state) (c : com)
                            : state :=
    match c with
      | SKIP ⇒
          st
      | x ::= a1 ⇒
          (x !-> (aeval st a1) ; st)
      | c1 ;; c2 ⇒
          let st' := ceval_fun_no_while st c1 in
          ceval_fun_no_while st' c2
      | TEST b THEN c1 ELSE c2 FI ⇒
          if (beval st b)
            then ceval_fun_no_while st c1
            else ceval_fun_no_while st c2
      | WHILE b DO c END ⇒
          st (* bogus *)
    end.
  Close Scope imp_scope.
-/

def ceval_fun_no_while : state → com → state
  | st SKIP := st
  | st (x ::= a₁) := x !→ (aeval st a₁) ; st
  | st (c₁ ;; c₂) :=
    let st' := ceval_fun_no_while st c₁ in
    ceval_fun_no_while st' c₂
  | st (TEST b THEN c₁ ELSE c₂ FI) :=
      if (beval st b)
        then ceval_fun_no_while st c₁
        else ceval_fun_no_while st c₂
  | st (WHILE b DO c END) :=
      /- bogus -/
      st

/-
  TODO : point out how meta gets rid of the totality restriction
-/
meta def ceval_fun : state → com → state
  | st SKIP := st
  | st (x ::= a₁) := x !→ (aeval st a₁) ; st
  | st (c₁ ;; c₂) :=
    let st' := ceval_fun st c₁ in
    ceval_fun st' c₂
  | st (TEST b THEN c₁ ELSE c₂ FI) :=
      if (beval st b)
        then ceval_fun st c₁
        else ceval_fun st c₂
  | st (WHILE b DO c END) :=
      if (beval st b)
        then ceval_fun st (c ;; WHILE b DO c END)
        else st

#eval (ceval_fun empty_st subtract_3_from_5_slowly) Z

/-
  Reserved Notation "st '=[' c ']⇒' st'"
                    (at level 40).
  Inductive ceval : com → state → state → Prop :=
    | E_Skip : ∀st,
        st =[ SKIP ]⇒ st
    | E_Ass : ∀st a1 n x,
        aeval st a1 = n →
        st =[ x ::= a1 ]⇒ (x !-> n ; st)
    | E_Seq : ∀c1 c2 st st' st'',
        st =[ c1 ]⇒ st' →
        st' =[ c2 ]⇒ st'' →
        st =[ c1 ;; c2 ]⇒ st''
    | E_IfTrue : ∀st st' b c1 c2,
        beval st b = true →
        st =[ c1 ]⇒ st' →
        st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
    | E_IfFalse : ∀st st' b c1 c2,
        beval st b = false →
        st =[ c2 ]⇒ st' →
        st =[ TEST b THEN c1 ELSE c2 FI ]⇒ st'
    | E_WhileFalse : ∀b st c,
        beval st b = false →
        st =[ WHILE b DO c END ]⇒ st
    | E_WhileTrue : ∀st st' st'' b c,
        beval st b = true →
        st =[ c ]⇒ st' →
        st' =[ WHILE b DO c END ]⇒ st'' →
        st =[ WHILE b DO c END ]⇒ st''

    where "st =[ c ]⇒ st'" := (ceval c st st').
-/

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

open ceval

local notation st ` =[ ` c ` ]⇒ ` st' := ceval c st st'

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
    (* We must supply the intermediate state *)
    apply E_Seq with (X !-> 2).
    - (* assignment command *)
      apply E_Ass. reflexivity.
    - (* if command *)
      apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.
  Qed.
-/

example :
  empty_st =[
    X ::= 2;;
    TEST X ≤ 1
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
  Example ceval_example2:
    empty_st =[
      X ::= 0;; Y ::= 1;; Z ::= 2
    ]⇒ (Z !-> 2 ; Y !-> 1 ; X !-> 0).
  Proof.
    (* FILL IN HERE *) Admitted.
-/

example :
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]⇒ Z !→ 2 ; Y !→ 1 ; X !→ 0 :=
begin
  apply E_Seq,
    apply E_Seq,
      apply E_Ass,
      refl,
    apply E_Ass,
    refl,
  apply E_Ass,
  refl,
end

/-
  Definition pup_to_n : com
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Theorem pup_to_2_ceval :
    (X !-> 2) =[
      pup_to_n
    ]⇒ (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
  Proof.
    (* FILL IN HERE *) Admitted.
-/

def pup_to_n : com :=
  Y ::= 0;;
  WHILE ¬X == 0 DO
    Y ::= Y + X;;
    X ::= X - 1
  END

theorem pup_to_2_ceval :
  X !→ 2 =[
    pup_to_n
  ]⇒ X !→ 0 ; Y !→ 3 ; X !→ 1 ; Y !→ 2 ; Y !→ 0 ; X !→ 2 :=
begin
  unfold pup_to_n,
  apply E_Seq,
    apply E_Ass,
    refl,
  apply E_WhileTrue,
      refl,
    apply E_Seq,
      apply E_Ass,
      refl,
    apply E_Ass,
    refl,
  apply E_WhileTrue,
      refl,
    apply E_Seq,
      apply E_Ass,
      refl,
    apply E_Ass,
    refl,
  apply E_WhileFalse,
  refl,
end

/-
  Theorem ceval_deterministic: ∀c st st1 st2,
      st =[ c ]⇒ st1 →
      st =[ c ]⇒ st2 →
      st1 = st2.
  Proof.
    intros c st st1 st2 E1 E2.
    generalize dependent st2.
    induction E1;
            intros st2 E2; inversion E2; subst.
    - (* E_Skip *) reflexivity.
    - (* E_Ass *) reflexivity.
    - (* E_Seq *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.
    - (* E_IfTrue, b1 evaluates to true *)
        apply IHE1. assumption.
    - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
        rewrite H in H5. discriminate H5.
    - (* E_IfFalse, b1 evaluates to true (contradiction) *)
        rewrite H in H5. discriminate H5.
    - (* E_IfFalse, b1 evaluates to false *)
        apply IHE1. assumption.
    - (* E_WhileFalse, b1 evaluates to false *)
      reflexivity.
    - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
      rewrite H in H2. discriminate H2.
    - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
      rewrite H in H4. discriminate H4.
    - (* E_WhileTrue, b1 evaluates to true *)
        assert (st' = st'0) as EQ1.
        { (* Proof of assertion *) apply IHE1_1; assumption. }
        subst st'0.
        apply IHE1_2. assumption. Qed.
-/

theorem ceval_deterministic {c st st₁ st₂}
  (e₁ : st =[ c ]⇒ st₁) (e₂ : st =[ c ]⇒ st₂) : st₁ = st₂ :=
begin
  induction e₁ generalizing st₂,
  case E_Skip {
    cases e₂,
    refl,
  },
  case E_Ass : st' a₁ n x a {
    with_cases {cases e₂},
    case E_Ass : n' a' {
      subst a,
      subst a',
      refl,
    },
  },
  case E_Seq : c₁ c₂ st' st'' st''' a₁ a₂ ih₁ ih₂ {
    with_cases {cases e₂},
    case E_Seq : st'''' a₁' a₂' {
      apply ih₂,
      have : st'' = st'''',
        exact ih₁ a₁',
      rwa ←this at a₂',
    },
  },
  case E_IfTrue : st' st'' b c₁ c₂ a₁ a₂ ih {
    with_cases {cases e₂},
    case E_IfTrue : a₁' a₂' { exact ih a₂', },
    case E_IfFalse : a₁' a₂' {
      rw a₁ at a₁',
      contradiction,
    },
  },
  case E_IfFalse : st' st'' b c₁ c₂ a₁ a₂ ih {
    with_cases {cases e₂},
    case E_IfTrue: a₁' a₂' {
      rw a₁ at a₁',
      contradiction,
    },
    case E_IfFalse : a₁' a₂' { exact ih a₂', },
  },
  case E_WhileFalse : b st' c a {
    with_cases {cases e₂},
    case E_WhileFalse : a₁ a₂ { refl, },
    case E_WhileTrue : st'' a' a₁ a₂ {
      rw a at a',
      contradiction,
    },
  },
  case E_WhileTrue : st' st'' st''' b c a a₁ a₂ ih₁ ih₂ {
    with_cases {cases e₂},
    case E_WhileFalse : a' h₁ {
      rw a at a',
      contradiction,
    },
    case E_WhileTrue : st'''' a' a₁' a₂' {
      apply ih₂,
      have : st'' = st'''',
        exact ih₁ a₁',
      rwa ←this at a₂',
    },
  },
end

/-
  Theorem plus2_spec : ∀st n st',
    st X = n →
    st =[ plus2 ]⇒ st' →
    st' X = n + 2.
  Proof.
    intros st n st' HX Heval.
    inversion Heval. subst. clear Heval. simpl.
    apply t_update_eq. Qed.
-/

theorem plus₂_spec {st : state} {st' n}
  (hx : st X = n) (heval : st =[ plus₂ ]⇒ st')
  : st' X = n + 2 :=
begin
  with_cases {cases heval},
  case : n' hx' {
    subst hx,
    subst hx',
    refl,
  },
end

theorem XtimesYinZ_spec {st : state} {x y st'}
  (hx : st X = x)
  (hy : st Y = y)
  (h : st =[ XtimesYinZ ]⇒ st')
  : st' Z = x * y :=
begin
  with_cases {cases h},
  case : n a {
    subst a,
    subst hx,
    subst hy,
    unfold aeval,
    refl,
  },
end

/-
  Theorem loop_never_stops : ∀st st',
    ~(st =[ loop ]⇒ st').
  Proof.
    intros st st' contra. unfold loop in contra.
    remember (WHILE true DO SKIP END)%imp as loopdef
            eqn:Heqloopdef.
    Admitted.
-/

theorem loop_never_stops {st st'} : not (st =[ loop ]⇒ st') :=
begin
  by_contra contra,
  unfold loop at contra,
  generalize heq : WHILE tt DO SKIP END = loopdef,
  rw heq at contra,
  induction contra; try { contradiction },
  case E_WhileFalse : b st'' c a {
    injection heq with heq₁ heq₂,
    rw ←heq₁ at a,
    cases a,
  }
end

/-
  Open Scope imp_scope.
  Fixpoint no_whiles (c : com) : bool :=
    match c with
    | SKIP ⇒
        true
    | _ ::= _ ⇒
        true
    | c1 ;; c2 ⇒
        andb (no_whiles c1) (no_whiles c2)
    | TEST _ THEN ct ELSE cf FI ⇒
        andb (no_whiles ct) (no_whiles cf)
    | WHILE _ DO _ END ⇒
        false
    end.
  Close Scope imp_scope.
-/

def no_whiles : com → bool
  | SKIP := tt
  | (_ ::= _) := tt
  | (c₁ ;; c₂) := band (no_whiles c₁) (no_whiles c₂)
  | (TEST _ THEN ct ELSE cf FI) := band (no_whiles ct) (no_whiles cf)
  | (WHILE _ DO _ END) := ff

/-
  Inductive no_whilesR: com → Prop :=
  (* FILL IN HERE *)
  .
  Theorem no_whiles_eqv:
    ∀c, no_whiles c = true ↔ no_whilesR c.
  Proof.
    (* FILL IN HERE *) Admitted.
-/

inductive no_whilesR : com → Prop
  | N_Skip : no_whilesR SKIP
  | N_Ass : ∀s a, no_whilesR (s ::= a)
  | N_Seq : ∀{c₁ c₂},
    no_whilesR c₁ →
    no_whilesR c₂ →
    no_whilesR (c₁ ;; c₂)
  | N_If : ∀b {c₁ c₂},
    no_whilesR c₁ →
    no_whilesR c₂ →
    no_whilesR (TEST b THEN c₁ ELSE c₂ FI)

open no_whilesR

theorem no_while_eqv {c} : no_whiles c = tt ↔ no_whilesR c :=
begin
  split,
    intro h,
    induction c,
    case CSkip { constructor, },
    case CAss : x a { constructor, },
    case CSeq : c₁ c₂ ih₁ ih₂ {
      unfold no_whiles at h,
      simp only [band_eq_true_eq_eq_tt_and_eq_tt] at h,
      exact N_Seq (ih₁ h.left) (ih₂ h.right),
    },
    case CIf : b c₁ c₂ ih₁ ih₂ {
      unfold no_whiles at h,
      simp only [band_eq_true_eq_eq_tt_and_eq_tt] at h,
      exact N_If b (ih₁ h.left) (ih₂ h.right),
    },
    case CWhile : b c ih {
      unfold no_whiles at h,
      contradiction,
    },
  intro h,
  induction h,
  case N_Skip { unfold no_whiles, },
  case N_Ass : s a { unfold no_whiles, },
  case N_Seq : c₁ c₂ h₁ h₂ ih₁ ih₂ {
    unfold no_whiles,
    rw [ih₁, ih₂],
    unfold band,
  },
  case N_If : b c₁ c₂ h₁ h₂ ih₁ ih₂ {
    unfold no_whiles,
    rw [ih₁, ih₂],
    unfold band,
  }
end

theorem no_whiles_terminating (st) {c} (h : no_whilesR c)
  : ∃st', st =[ c ]⇒ st' :=
begin
  induction h generalizing st,
  case N_Skip { exact ⟨st, E_Skip st⟩, },
  case N_Ass : s a {
    generalize heq : aeval st a = n,
    exact ⟨s !→ n ; st, E_Ass s heq⟩,
  },
  case N_Seq : c₁ c₂ h₁ h₂ ih₁ ih₂ {
    cases ih₁ st with st' ih₁,
    cases ih₂ st' with st'' ih₂,
    exact ⟨st'', E_Seq ih₁ ih₂⟩,
  },
  case N_If : b c₁ c₂ h₁ h₂ ih₁ ih₂ {
    generalize heq : beval st b = b',
    cases b',
      cases ih₂ st with st' ih₂,
      exact ⟨st', E_IfFalse c₁ heq ih₂⟩,
    cases ih₁ st with st' ih₁,
    exact ⟨st', E_IfTrue c₂ heq ih₁⟩,
  },
end

/-
  Inductive sinstr : Type :=
  | SPush (n : nat)
  | SLoad (x : string)
  | SPlus
  | SMinus
  | SMult.
-/

inductive sinstr : Type
  | SPush (n : ℕ)
  | SLoad (x : string)
  | SPlus
  | SMinus
  | SMult

open sinstr

/-
  Fixpoint s_execute (st : state) (stack : list nat)
                    (prog : list sinstr)
                  : list nat
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Example s_execute1 :
      s_execute empty_st []
        [SPush 5; SPush 3; SPush 1; SMinus]
    = [2; 5].
  (* FILL IN HERE *) Admitted.

  Example s_execute2 :
      s_execute (X !-> 3) [3;4]
        [SPush 4; SLoad X; SMult; SPlus]
    = [15; 4].
  (* FILL IN HERE *) Admitted.
-/

def s_execute' (st : state) : list ℕ → list sinstr → list ℕ
  | stack [] := stack
  | stack (SPush n::ins) := s_execute' (n::stack) ins
  | stack (SLoad x::ins) := s_execute' (aeval st x::stack) ins
  | (n₂::n₁::stack) (SPlus::ins) := s_execute' ((n₁ + n₂)::stack) ins
  | (n₂::n₁::stack) (SMinus::ins) := s_execute' ((n₁ - n₂)::stack) ins
  | (n₂::n₁::stack) (SMult::ins) := s_execute' ((n₁ * n₂)::stack) ins
  | stack (_::ins) := s_execute' stack ins

/- order really matters -/
def s_execute (st : state) : list sinstr → list ℕ → list ℕ
  | [] stack := stack
  | (SPush n::ins) stack := s_execute ins (n::stack)
  | (SLoad x::ins) stack := s_execute ins (aeval st x::stack)
  | (SPlus::ins) (n₂::n₁::stack) := s_execute ins ((n₁ + n₂)::stack)
  | (SMinus::ins) (n₂::n₁::stack) := s_execute ins ((n₁ - n₂)::stack)
  | (SMult::ins) (n₂::n₁::stack) := s_execute ins ((n₁ * n₂)::stack)
  | (_::ins) stack := s_execute ins stack

#print s_execute'._main
#print s_execute._main

example : s_execute
  empty_st [SPush 5, SPush 3, SPush 1, SMinus] [] = [2, 5] := rfl

example : s_execute
  (X !→ 3) [SPush 4, SLoad X, SMult, SPlus] [3, 4] = [15, 4] := rfl

/-
  Fixpoint s_compile (e : aexp) : list sinstr
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def s_compile : aexp → list sinstr
  | (ANum n) := [SPush n]
  | (AId x) := [SLoad x]
  | (APlus a₁ a₂) := s_compile a₁ ++ s_compile a₂ ++ [SPlus]
  | (AMinus a₁ a₂) := s_compile a₁ ++ s_compile a₂ ++ [SMinus]
  | (AMult a₁ a₂) := s_compile a₁ ++ s_compile a₂ ++ [SMult]

/-
  Example s_compile1 :
    s_compile (X - (2 * Y))%imp
    = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
  (* FILL IN HERE *) Admitted.
-/

example : s_compile X = [SLoad X] := rfl

/-
  TODO - notation for numbers is broke af
-/
example : s_compile (ANum 2) = [SPush 2] := rfl

example : s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X, SPush 2, SLoad Y, SMult, SMinus] := rfl

/-
  Theorem s_compile_correct : ∀(st : state) (e : aexp),
    s_execute st [] (s_compile e) = [ aeval st e ].
  Proof.
    (* FILL IN HERE *) Admitted.
-/

#print s_execute._main
#print s_execute'._main

theorem s_execute_app (st stack l₁ l₂)
  : s_execute st (l₁ ++ l₂) stack =
    s_execute st l₂ (s_execute st l₁ stack) :=
begin
  induction l₁ generalizing st stack l₂,
  case nil { refl, },
  case cons : h t ih {
    simp,
    induction h,
    case SPush {
      unfold s_execute,
      rw ih,
    },
    case SLoad {
      unfold s_execute,
      rw ih,
    },
    case SPlus {
      cases stack with h₁ t₁,
        unfold s_execute,
        rw ih,
      cases t₁ with h₂ t₂,
        unfold s_execute,
        rw ih,
      unfold s_execute,
      rw ih,
    },
    case SMinus {
      cases stack with h₁ t₁,
        unfold s_execute,
        rw ih,
      cases t₁ with h₂ t₂,
        unfold s_execute,
        rw ih,
      unfold s_execute,
      rw ih,
    },
    case SMult {
      cases stack with h₁ t₁,
        unfold s_execute,
        rw ih,
      cases t₁ with h₂ t₂,
        unfold s_execute,
        rw ih,
      unfold s_execute,
      rw ih,
    },
  },
end

theorem s_execute_app' (st stack l₁ l₂)
  : s_execute st (l₁ ++ l₂) stack =
    s_execute st l₂ (s_execute st l₁ stack) :=
begin
  induction l₁ generalizing stack,
  case nil { refl, },
  case cons : h t ih {
    cases h;
    repeat { simp [s_execute, ih] <|> cases stack with hd stack, },
  },
end

theorem s_compile_correct' (st stack e)
  : s_execute st (s_compile e) stack = aeval st e::stack :=
begin
  induction e generalizing st stack;
    simp [s_compile, s_execute, aeval, s_execute_app, *];
    refl,
end

theorem s_compile_correct (st e)
  : s_execute st (s_compile e) [] = [ aeval st e ] :=
s_compile_correct' st [] e

def beval' (st : state): bexp → bool
  | BTrue := tt
  | BFalse := ff
  | (BEq a₁ a₂) := aeval st a₁ = aeval st a₂
  | (BLe a₁ a₂) := aeval st a₁ ≤ aeval st a₂
  | (BNot b₁) := ¬beval' b₁
  | (BAnd b₁ b₂) := if beval' b₁ then beval' b₂ else ff

theorem beval_equiv (st b) : beval' st b = beval st b :=
begin
  induction b; simp [beval', beval],
  case BNot : b ih { rwa ih, },
  case BAnd : b₁ b₂ ih₁ ih₂ {
    cases (beval st b₁);
    cases (beval st b₂);
    simp [ih₁, ih₂],
  },
end

namespace break_imp

/-
  Inductive com : Type :=
    | CSkip
    | CBreak (* <--- NEW *)
    | CAss (x : string) (a : aexp)
    | CSeq (c1 c2 : com)
    | CIf (b : bexp) (c1 c2 : com)
    | CWhile (b : bexp) (c : com).

  Notation "'SKIP'" :=
    CSkip.
  Notation "'BREAK'" :=
    CBreak.
  Notation "x '::=' a" :=
    (CAss x a) (at level 60).
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
    (CIf c1 c2 c3) (at level 80, right associativity).
-/

inductive com
  | CSkip
  | CBreak /- NEW -/
  | CAss (x : string) (a : aexp)
  | CSeq (c₁ c₂ : com)
  | CIf (b : bexp) (c₁ c₂ : com)
  | CWhile (b : bexp) (c : com)

open com

local notation `SKIP` := CSkip
local notation `BREAK` := CBreak
local infix ` ::= `:60 := CAss
local infix ` ;; `:35 := CSeq
local notation `WHILE ` b ` DO ` c ` END` := CWhile b c
local notation `TEST ` c₁ ` THEN ` c₂ ` ELSE ` c₃ ` FI` := CIf c₁ c₂ c₃

/-
  Inductive result : Type :=
    | SContinue
    | SBreak.

  Reserved Notation "st '=[' c ']⇒' st' '/' s"
          (at level 40, st' at next level).
-/

inductive result : Type
  | SContinue
  | SBreak

open result

/-
  Inductive ceval : com → state → result → state → Prop :=
    | E_Skip : ∀st,
        st =[ CSkip ]⇒ st / SContinue
    (* FILL IN HERE *)
-/

inductive ceval : com → imp.state → result → imp.state → Prop
  | E_Skip : ∀st, ceval SKIP st SContinue st
  | E_Break : ∀st, ceval BREAK st SBreak st
  | E_Ass : ∀{st a₁ n} x,
    aeval st a₁ = n →
    ceval (x ::= a₁) st SContinue (x !→ n ; st)
  | E_SeqB : ∀{c₁ c₂ st st' r st''},
    ceval c₁ st SBreak st' →
    ceval c₂ st' r st'' →
    ceval (c₁ ;; c₂) st SBreak st'
  | E_SeqC : ∀{c₁ c₂ st st' r st''},
    ceval c₁ st SContinue st' →
    ceval c₂ st' r st'' →
    ceval (c₁ ;; c₂) st r st''
  | E_IfTrue : ∀{st r st' b c₁} c₂,
    beval st b = tt →
    ceval c₁ st r st' →
    ceval (TEST b THEN c₁ ELSE c₂ FI) st r st'
  | E_IfFalse : ∀{st r st' b} c₁ {c₂},
    beval st b = ff →
    ceval c₂ st r st' →
    ceval (TEST b THEN c₁ ELSE c₂ FI) st r st'
  | E_WhileFalse : ∀{b st} c,
    beval st b = ff →
    ceval (WHILE b DO c END) st SContinue st
  | E_WhileTrueB : ∀{st st' b c},
    beval st b = tt →
    ceval c st SBreak st' →
    ceval (WHILE b DO c END) st SContinue st'
  | E_WhileTrueC : ∀{st st' st'' b c},
    beval st b = tt →
    ceval c st SContinue st' →
    ceval (WHILE b DO c END) st' SContinue st'' →
    ceval (WHILE b DO c END) st SContinue st''

open ceval

/- issues with single slash -/
notation st ` =[ ` c ` ]⇒ ` st' ` // ` s := ceval c st s st'

/-
  Theorem break_ignore : ∀c st st' s,
      st =[ BREAK;; c ]⇒ st' / s →
      st = st'.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem while_continue : ∀b c st st' s,
    st =[ WHILE b DO c END ]⇒ st' / s →
    s = SContinue.
  Proof.
    (* FILL IN HERE *) Admitted.

  Theorem while_stops_on_break : ∀b c st st',
    beval st b = true →
    st =[ c ]⇒ st' / SBreak →
    st =[ WHILE b DO c END ]⇒ st' / SContinue.
  Proof.
    (* FILL IN HERE *) Admitted.
-/

/-
  TODO: these should all be easy to prove
  if you find yourself doing something complicated,
  your definition of ceval is probably wrong
-/

theorem break_ignore {c st st' s}
  (h : st =[ BREAK ;; c ]⇒ st' // s)
  : st = st' :=
begin
  cases h,
  case E_SeqB {
    revert_after st',
    intros r st'' h h₁ h₂,
    cases h₂,
    refl,
  },
  case E_SeqC {
    revert_after st',
    intros s st'' h₁ h₂,
    cases h₁,
  },
end

theorem while_continue {b c st st' s}
  (h : st =[ WHILE b DO c END ]⇒ st' // s)
  : s = SContinue := by cases h; refl

theorem while_stops_on_break {b c st st'}
  (hb : beval st b = tt)
  (hc : st =[ c ]⇒ st' // SBreak)
  : st =[ WHILE b DO c END ]⇒ st' // SContinue :=
    E_WhileTrueB hb hc

/-
  Theorem while_break_true : ∀b c st st',
    st =[ WHILE b DO c END ]⇒ st' / SContinue →
    beval st' b = true →
    ∃st'', st'' =[ c ]⇒ st' / SBreak.
  Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem while_break_true {b c st st'}
  (hc : st =[ WHILE b DO c END ]⇒ st' // SContinue)
  (hb : beval st' b = tt)
  : ∃st'', st'' =[ c ]⇒ st' // SBreak :=
begin
  generalize heq : WHILE b DO c END = c',
  rw heq at hc,
  induction hc; try { trivial, },
  case E_WhileFalse : b' st'' c'' hb' {
    injection heq with hl hr,
    subst hl,
    rw hb at hb',
    contradiction,
  },
  case E_WhileTrueB : st'' st''' b' c'' hb' hc ih {
    injection heq with hl hr,
    subst hr,
    exact ⟨st'', hc⟩,
  },
  case E_WhileTrueC : st'' st''' st'''' b' c'' hb' hc₁ hc₂ ih₁ ih₂ {
    exact ih₂ hb heq,
  },
end

/-
  Theorem ceval_deterministic: ∀(c:com) st st1 st2 s1 s2,
      st =[ c ]⇒ st1 / s1 →
      st =[ c ]⇒ st2 / s2 →
      st1 = st2 ∧ s1 = s2.
  Proof.
    (* FILL IN HERE *) Admitted.
-/

/-
  TODO - fixup naming
-/

theorem ceval_deterministic {c st st₁ st₂ s₁ s₂}
  (hc₁ : st =[ c ]⇒ st₁ // s₁)
  (hc₂ : st =[ c ]⇒ st₂ // s₂)
  : st₁ = st₂ ∧ s₁ = s₂ :=
begin
  induction hc₁ generalizing st₂ s₂,
  case E_Skip {
    cases hc₂,
    split; refl,
  },
  case E_Break {
    cases hc₂,
    split; refl,
  },
  case E_Ass : st' a₁ n x h {
    with_cases { cases hc₂, },
    case : n' h' {
      rw h at h',
      subst h',
      split; refl,
    },
  },
  case E_SeqB : c₁ c₂ st' st'' r st''' hc₁ hc₂' ih₁ ih₂ {
    cases hc₂,
    case E_SeqB : _ _ _ _ r' st'''' hc₁' hc₂'' {
      exact ih₁ hc₁',
    },
    case E_SeqC : _ _ _ _ _ st'''' hc₁' hc₂'' {
      cases ih₁ hc₁',
      contradiction,
    },
  },
  case E_SeqC : c₁ c₂ st' st'' r st''' hc₁ hc₂' ih₁ ih₂ {
    cases hc₂,
    case E_SeqB : _ _ _ _ r' st'''' hc₁' hc₂'' {
      cases ih₁ hc₁',
      contradiction,
    },
    case E_SeqC : _ _ _ _ _ st'''' hc₁' hc₂'' {
      rw ←(ih₁ hc₁').left at hc₂'',
      exact ih₂ hc₂'',
    },
  },
  case E_IfTrue : st' r st'' b c₁ c₂ h₁ h₂ ih {
    cases hc₂,
    case E_IfTrue : _ _ _ _ _ _ hb₂ hc₂ { exact ih hc₂, },
    case E_IfFalse : _ _ _ _ _ _ hb₂ hc₂ {
      rw h₁ at hb₂,
      contradiction,
    },
  },
  case E_IfFalse : st' r st'' b c₁ c₂ hb₁ hc₁ ih {
    cases hc₂,
    case E_IfTrue : _ _ _ _ _ _ hb₂ hc₂ {
      rw hb₁ at hb₂,
      contradiction,
    },
    case E_IfFalse : _ _ _ _ _ _ hb₂ hc₂ { exact ih hc₂, },
  },
  case E_WhileFalse : b st' c' hb₁ {
    cases hc₂,
    case E_WhileFalse : hb₂ hc₂ { split; refl, },
    case E_WhileTrueB : _ _ _ _ hb₂ hc₂' {
      rw hb₁ at hb₂,
      contradiction,
    },
    case E_WhileTrueC : _ _ _ _ st'' hb₂ hc₂' hc₂'' {
      rw hb₁ at hb₂,
      contradiction,
    },
  },
  case E_WhileTrueB : st' st'' b c' hb₁ hc₁ ih {
    cases hc₂,
    case E_WhileFalse : _ _ _ hb₂ {
      rw hb₁ at hb₂,
      contradiction,
    },
    case E_WhileTrueB : _ _ _ _ hb₂ hc₂' {
      rw (ih hc₂').left,
      split; refl,
    },
    case E_WhileTrueC : _ _ _ _ st''' hb₂ hc₂' hc₂'' {
      cases ih hc₂',
      contradiction,
    },
  },
  case E_WhileTrueC : st' st'' st''' b c' hb₁ hc₁' hc₁'' ih₁ ih₂ {
    cases hc₂,
    case E_WhileFalse : _ _ _ hb₂ {
      rw hb₁ at hb₂,
      contradiction,
    },
    case E_WhileTrueB : _ _ _ _ hb₂ hc₂' {
      cases ih₁ hc₂',
      contradiction,
    },
    case E_WhileTrueC : _ _ _ _ st'''' hb₂ hc₂' hc₂'' {
      rw ←(ih₁ hc₂').left at hc₂'',
      exact ih₂ hc₂'',
    },
  },
end

end break_imp

local notation `FOR ` intr ` ;;; ` cond ` ;;; ` up ` DO ` body ` END` :=
  intr ;; WHILE cond DO body ;; up END

def sum_to (n) :=
  FOR X ::= n ;; Y ::= 0 ;;; ¬X == 0 ;;; X ::= X - 1 DO
    Y ::= Y + X
  END

#eval (ceval_fun empty_st $ sum_to 5) Y

end imp