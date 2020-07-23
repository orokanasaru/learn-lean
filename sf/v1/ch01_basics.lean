import tactic.basic

namespace basics

/-
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
-/

inductive day : Type
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday

/- add open because coq puts constructors in scope -/
open day

/-
Definition next_weekday (d:day) : day :=
  match d with
  | monday ⇒ tuesday
  | tuesday ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday ⇒ friday
  | friday ⇒ monday
  | saturday ⇒ monday
  | sunday ⇒ monday
  end.
-/

def next_weekday : day → day
| monday := tuesday
| tuesday := wednesday
| wednesday := thursday
| thursday := friday
| _ := monday

/-
Compute (next_weekday friday).
(* ==> monday : day *)
Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)
-/

#reduce next_weekday friday
#reduce next_weekday (next_weekday saturday)

/-
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.
-/

example : next_weekday (next_weekday saturday) = tuesday := rfl

/-
Inductive bool : Type :=
  | true
  | false.
-/

/- tt/ff are always in scope and the compiler will pick them over your impl -/
namespace myBool

inductive bool : Type
| tt
| ff

end myBool

/-
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ true
  | false ⇒ b2
  end.
-/

def bnot : bool → bool
| tt := ff
| _ := tt

def band : bool → bool → bool
| tt b₂ := b₂
| _ _ := ff

def bor : bool → bool → bool
| ff b₂ := b₂
| _ _ := tt

/-
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
-/

example : bor tt ff = tt := rfl
example : bor ff ff = ff := rfl
example : bor ff tt = tt := rfl
example : bor tt tt = tt := rfl

/-
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
-/

local infix && := band
local infix || := bor

example : ff || ff || tt = tt := rfl

/-
Definition nandb (b1:bool) (b2:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_nandb1: (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2: (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3: (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4: (nandb true true) = false.
(* FILL IN HERE *) Admitted.
-/

def bnand : bool → bool → bool
| tt tt := ff
| _ _ := tt

example : bnand tt ff = tt := rfl
example : bnand ff ff = tt := rfl
example : bnand ff tt = tt := rfl
example : bnand tt tt = ff := rfl

/-
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_andb31: (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32: (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33: (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34: (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
-/

def band3 (b₁ : bool) (b₂ : bool) (b₃ : bool) : bool :=
  band b₁ (band b₂ b₃)

example : band3 tt tt tt = tt := rfl
example : band3 ff tt tt = ff := rfl
example : band3 tt ff tt = ff := rfl
example : band3 tt tt ff = ff := rfl

/-
Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)
-/

#check tt
#check bnot tt

/-
Check negb.
(* ===> negb : bool -> bool *)
-/

#check bnot

/-
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
-/

inductive rgb : Type
| red
| green
| blue

inductive color : Type
| black
| white
| primary (p : rgb)

open rgb
open color

/-
Definition monochrome (c : color) : bool :=
  match c with
  | black ⇒ true
  | white ⇒ true
  | primary q ⇒ false
  end.
-/

def monochrome : color → bool
| black := tt
| white := tt
| _ := ff

/-
Definition isred (c : color) : bool :=
  match c with
  | black ⇒ false
  | white ⇒ false
  | primary red ⇒ true
  | primary _ ⇒ false
  end.
-/

def isred : color → bool
| (primary red) := tt
| _ := false

/-
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0).
(* ==> bits B1 B0 B1 B0 : nybble *)
-/

inductive bit : Type
| B₀
| B₁

open bit

inductive nybble : Type
| bits (b₀ b₁ b₂ b₃ : bit)

open nybble

#check bits B₁ B₀ B₁ B₀

/-
Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) ⇒ true
    | (bits _ _ _ _) ⇒ false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)
-/

def all_zero : nybble → bool
| (bits B₀ B₀ B₀ B₀) := tt
| _ := ff

/-
Module NatPlayground.
-/

namespace myNat

/-
Inductive nat : Type :=
  | O
  | S (n : nat).
-/

inductive nat : Type
| zero
| succ (n : nat)

end myNat

/-
Inductive nat' : Type :=
  | stop
  | tick (foo : nat').
-/

inductive nat' : Type
| stop
| tick (foo : nat')

/-
Definition pred (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ n'
  end.
-/

open nat (succ zero)

def pred : ℕ → ℕ
| zero := zero
| (succ n) := n

/-
Check (S (S (S (S O)))).
  (* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S O ⇒ O
    | S (S n') ⇒ n'
  end.

Compute (minustwo 4).
  (* ===> 2 : nat *)
-/

#check succ (succ (succ (succ zero)))

def sub_two : ℕ → ℕ
| (succ (succ n)) := n
| _ := zero

#reduce sub_two 4

/-
Check S.
Check pred.
Check minustwo.
-/

#check succ
#check pred
#check sub_two

/-
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ evenb n'
  end.
-/

/- recursion just works with this form -/
def evenb : ℕ → bool
| 0 := tt
| 1 := ff
| (succ (succ n)) := evenb n

/-
Definition oddb (n:nat) : bool := negb (evenb n).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.
-/

def oddb := bnot ∘ evenb

example : oddb 1 = tt := rfl
example : oddb 4 = ff := rfl

/-
Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.
-/

/-
TODO: lean recurses on the right argument
-/
def add : ℕ → ℕ → ℕ
| 0 m := m
| (n + 1) m := (add n m) + 1

/-
Compute (plus 3 2).
-/

#reduce add 3 2

/-
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.
-/

/-
TODO: lean recurses on the right argument
match doesn't work with recursion
-/
def mul : ℕ → ℕ → ℕ
| 0 m := 0
| (n + 1) m := add m (mul n m)

/-
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ ⇒ O
  | S _ , O ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O ⇒ S O
    | S p ⇒ mult base (exp base p)
  end.
-/

def sub : ℕ → ℕ → ℕ
| 0 _ := 0
| n 0 := n
| (n + 1) (m + 1) := sub n m

/- left of the colon is fixed in recursive calls -/
def exp (base : ℕ) : ℕ → ℕ
| 0 := 1
| (p + 1) := mul base (exp p)

/-
Fixpoint factorial (n:nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_factorial1: (factorial 3) = 6.
(* FILL IN HERE *) Admitted.

Example test_factorial2: (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
-/

def factorial : ℕ → ℕ
| 0 := 1
| (n + 1) := mul (n + 1) (factorial n)

example : factorial 3 = 6 := rfl
example : factorial 5 = mul 10 12 := rfl

/-
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).
-/

/- actual definitions use type classes -/
/- this breaks the ability to pattern match on + 1 instead of succ -/
local infixl + := add
local infixl - := sub
local infixl * := mul

#check ((0 + 1) + 1)

/-
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ eqb n' m'
            end
  end.
-/

def eqb : ℕ → ℕ → bool
| 0 0 := tt
| 0 (succ m) := ff
| _ 0 := ff
| (succ n) (succ m) := eqb n m

/-
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O ⇒ true
  | S n' ⇒
      match m with
      | O ⇒ false
      | S m' ⇒ leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.
-/

/-
TODO - examine why wildcard on left breaks things
-/
def leb : ℕ → ℕ → bool
| 0 _ := tt
| (succ n) 0 := ff
| (succ n) (succ m) := leb n m

example : leb 2 2 = tt := rfl
example : leb 0 2 = tt := rfl
example : leb 4 2 = ff := rfl

/-
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.
-/

local infix ` =? `:50 := eqb
local infix ` ≤? `:50 := leb

example : (4 ≤? 2) = ff := rfl

/-
Definition ltb (n m : nat) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
(* FILL IN HERE *) Admitted.

Example test_ltb2: (ltb 2 4) = true.
(* FILL IN HERE *) Admitted.

Example test_ltb3: (ltb 4 2) = false.
(* FILL IN HERE *) Admitted.
-/

def ltb : ℕ → ℕ → bool
| _ 0 := ff
| 0 (succ m) := tt
| (succ n) (succ m) := ltb n m

local infix ` <? `:50 := ltb

example : ltb 2 2 = ff := rfl
example : ltb 2 4 = tt := rfl
example : ltb 4 2 = ff := rfl

/-
Theorem plus_O_n : ∀n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
-/

theorem zero_add (n : ℕ) : 0 + n = n := by refl

/-
Theorem plus_O_n' : ∀n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
-/

theorem zero_add' (n : ℕ) : 0 + n = n := rfl

/-
Theorem plus_1_l : ∀n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : ∀n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
-/

theorem one_plus (n : ℕ) : 1 + n = succ n := rfl
theorem zero_mul (n : ℕ) : 0 * n = 0 := rfl

/-
Theorem plus_id_example : ∀n m:nat,
  n = m →
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite → H.
  reflexivity. Qed.
-/

example (n m : ℕ) (h : n = m) : n + n = m + m := by rw h

/-
Theorem plus_id_exercise : ∀n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem add_id (n m o : ℕ) (hnm : n = m) (hmo : m = o) :
  n + m = m + o := by rw [hnm, hmo]

/-
Theorem mult_0_plus : ∀n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite → plus_O_n.
  reflexivity. Qed.
-/

theorem zero_add_mul (n m : ℕ) : (0 + n) * m = n * m :=
  by rw zero_add

/-
Theorem mult_S_1 : ∀n m : nat,
  m = S n →
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.
  (* (N.b. This proof can actually be completed with tactics other than
     rewrite, but please do use rewrite for the sake of the exercise.) *)
-/

theorem mul_one_add (n m : ℕ) (h : m = succ n)
  : m * (1 + n) = m * m := by rw [one_plus, ←h]

/-
Theorem plus_1_neq_0_firsttry : ∀n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.
-/

/- sorry is reported when importing as well, so commenting this out -/
/-
theorem plus_one_neq_zero_firsttry (n : ℕ) : (n + 1) =? 0 = ff :=
begin
  try { simp },
  sorry
end
-/

/-
Theorem plus_1_neq_0 : ∀n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
-/

theorem add_one_neq_zero (n : ℕ) : (n + 1) =? 0 = ff :=
begin
  cases n,
    refl,
  refl,
end

/-
Theorem negb_involutive : ∀b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.
-/

theorem bnot_involutive (b : bool) : bnot (bnot b) = b :=
begin
  cases b,
    refl,
  refl,
end

/-
Theorem andb_commutative : ∀b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
-/

theorem band_commutative (b c : bool) : band b c = band c b :=
begin
  cases b,
    cases c,
      refl,
    refl,
  cases c,
    refl,
  refl,
end

/-
Theorem andb_commutative' : ∀b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.
-/

theorem band_commutative' (b c : bool) : band b c = band c b :=
begin
cases b,
case ff {
  cases c,
  case ff { refl, },
  case tt { refl, }
},
case tt {
  cases c,
  case ff { refl, },
  case tt { refl, },
},
end

/-
Theorem andb3_exchange :
  ∀b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.
-/

/- this is horrible without combinators or automation -/
theorem band3_exchange (b c d : bool)
  : band (band b c) d = band (band b d) c :=
begin
  cases b,
  case ff {
    cases c,
    case ff {
      cases d,
      case ff { refl, },
      case tt { refl, },
    },
    case tt {
      cases d,
      case ff { refl, },
      case tt { refl, },
    },
  },
  case tt {
    cases c,
    case ff {
      cases d,
      case ff { refl, },
      case tt { refl, },
    },
    case tt {
      cases d,
      case ff { refl, },
      case tt { refl, },
    },
  }
end

/-
Theorem plus_1_neq_0' : ∀n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  ∀b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
-/

/-
nb. requires mathlib
TODO: rintro doesn't have case labels
-/
theorem add_one_neq_zero' : ∀n, n + 1 =? 0 = ff :=
begin
  rintro ⟨n⟩,
    refl,
  refl,
end

theorem band_commutative'' : ∀b c, band b c = band c b :=
begin
  rintro ⟨b⟩ ⟨c⟩,
        refl,
      refl,
    refl,
  refl,
end

/-
Theorem andb_true_elim2 : ∀b c : bool,
  andb b c = true → c = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem band_true_elim2 (b c : bool) (h : band b c = tt)
  : c = tt :=
begin
  cases c,
    rw ←h,
    cases b,
      refl,
    refl,
  refl,
end

/-
Theorem zero_nbeq_plus_1 : ∀n : nat,
  0 =? (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem zero_nbeq_plus_one (n : ℕ) : 0 =? (n + 1) = ff :=
begin
  cases n,
    refl,
  refl,
end

/-
Theorem identity_fn_applied_twice :
  ∀(f : bool → bool),
  (∀(x : bool), f x = x) →
  ∀(b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem identity_fn_applied_twice
  (f : bool → bool)
  (h : ∀ x : bool, f x = x)
  (b : bool) : f (f b) = b := by rw [h, h]

theorem negation_fn_applied_twice
  (f : bool → bool)
  (h : ∀ x : bool, f x = bnot x)
  (b : bool) : f (f b) = b :=
begin
  rw [h, h],
  rw bnot_involutive,
end

/-
Theorem andb_eq_orb :
  ∀(b c : bool),
  (andb b c = orb b c) →
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
this is so much worse wihout at
TODO: revisit idea of intro in the type def
-/
theorem band_eq_bor (b c : bool) : band b c = bor b c → b = c :=
begin
  cases b,
    cases c,
      intro h,
      refl,
    rw [band, bor],
    intro h,
    rw h,
  rw [band, bor],
  intro h,
  rw h,
end

/-
Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).
-/

inductive bin : Type
| Z
| A (n : bin)
| B (n : bin)

open bin

/-
Fixpoint incr (m:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Fixpoint bin_to_nat (m:bin) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def incr : bin → bin
| Z := B Z
| (A b) := B b
| (B b) := A (incr b)

def bin_to_nat : bin → ℕ
| Z := 0
| (A b) := 2 * bin_to_nat b
| (B b) := 2 * bin_to_nat b + 1

def nat_to_bin : ℕ → bin
| 0 := Z
| (succ n) := incr (nat_to_bin n)

example : bin_to_nat (nat_to_bin 127) = 127 := rfl

end basics