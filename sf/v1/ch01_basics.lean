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

/- add simp because coq makes definitions available to tactics -/
@[simp]
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

example : next_weekday (next_weekday saturday) = tuesday := by simp

/-
Inductive bool : Type :=
  | true
  | false.
-/

/- there seem to be issues redefining bool -/
namespace bool

inductive bool : Type
| tt
| ff

end bool

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

@[simp]
def negb : bool → bool
| tt := ff
| _ := tt

@[simp]
def andb : bool → bool → bool
| tt b₂ := b₂
| _ _ := ff

@[simp]
def orb : bool → bool → bool
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

example : orb tt ff = tt := by simp
example : orb ff ff = ff := by simp
example : orb ff tt = tt := by simp
example : orb tt tt = tt := by simp

/-
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
-/

/-
still can't shadow the prelude
using precedence of equivalent notation in core
-/
infix ` &&' `:70 := andb
infix ` ||' `:65 := orb

example : ff ||' ff ||' tt = tt := by simp

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

@[simp]
def nandb : bool → bool → bool
| tt tt := ff
| _ _ := tt

example : nandb tt ff = tt := by simp
example : nandb ff ff = tt := by simp
example : nandb ff tt = tt := by simp
example : nandb tt tt = ff := by simp

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

@[simp]
def andb3 (b₁ : bool) (b₂ : bool) (b₃ : bool) : bool :=
  andb b₁ (andb b₂ b₃)

example : andb3 tt tt tt = tt := by simp
example : andb3 ff tt tt = ff := by simp
example : andb3 tt ff tt = ff := by simp
example : andb3 tt tt ff = ff := by simp

/-
Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)
-/

#check tt
#check negb tt

/-
Check negb.
(* ===> negb : bool -> bool *)
-/

#check negb

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

namespace NatPlayground

/-
Inductive nat : Type :=
  | O
  | S (n : nat).
-/

inductive nat' : Type
| zero
| succ (n : nat')

open nat'

/-
Inductive nat' : Type :=
  | stop
  | tick (foo : nat').
-/

inductive nat'' : Type
| stop
| tick (foo : nat')

/-
Definition pred (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ n'
  end.
-/

/- issues again with prelude stuff -/
def pred : nat' → nat'
| zero := zero
| (succ n) := n

/-
End NatPlayground.
-/

end NatPlayground

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

open nat

#check succ (succ (succ (succ zero)))

def minustwo : ℕ → ℕ
| (succ (succ n)) := n
| _ := zero

#reduce minustwo 4

/-
Check S.
Check pred.
Check minustwo.
-/

#check succ
#check pred
#check minustwo

/-
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ evenb n'
  end.
-/

/- recursion just works with this form -/
@[simp]
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

@[simp]
def oddb := negb ∘ evenb

/- no real reason to compare to tt/ff -/
example : oddb 1 := by simp [evenb, oddb]
example : ¬oddb 4 := by simp [evenb, oddb]

/-
Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.
-/

namespace NatPlayground2

@[simp]
def plus : ℕ → ℕ → ℕ
| 0 m := m
| (n + 1) m := (plus n m) + 1

/-
Compute (plus 3 2).
-/

#reduce plus 3 2

/-
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.
-/

/- match doesn't seem to work with recursion -/
@[simp]
def mult : ℕ → ℕ → ℕ
| 0 m := 0
| (n + 1) m := plus m (mult n m)

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

@[simp]
def minus : ℕ → ℕ → ℕ
| 0 _ := 0
| n 0 := n
| (n + 1) (m + 1) := minus n m

end NatPlayground2

open NatPlayground2

/- the differences for left and right of colon are so weird -/
@[simp]
def exp (base : ℕ) : ℕ → ℕ
| 0 := 1
| (p + 1) := mult base (exp p)

/-
Fixpoint factorial (n:nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_factorial1: (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2: (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
-/

@[simp]
def factorial : ℕ → ℕ
| 0 := 1
| (n + 1) := mult (n + 1) (factorial n)

example : factorial 3 = 6 := by simp
example : factorial 5 = mult 10 12 := by simp

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

infixl ` +' `:65 := plus
infixl ` -' `:65 := minus
infixl ` *' `:70 := mult

#check ((0 +' 1) +' 1)

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

@[simp]
def eqb : ℕ → ℕ → bool
| 0 0 := tt
| 0 (m + 1) := ff
| _ 0 := ff
| (n + 1) (m + 1) := eqb n m

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

@[simp]
def leb : ℕ → ℕ → bool
/- no idea why i can't just do this -/
/- 0 _ := tt -/
| 0 0 := tt
| 0 (m + 1) := tt
| _ 0 := ff
| (n + 1) (m + 1) := leb n m

#print leb._main

example : leb 2 2 := by simp
example : leb 0 2 := by simp
example : ¬leb 4 2 := by simp

/-
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.
-/

infix ` =? `:50 := eqb
infix ` <=? `:50 := leb

example : ¬(4 <=? 2) := by simp

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

@[simp]
def ltb : ℕ → ℕ → bool
| _ 0 := ff
| 0 (m + 1) := tt
| (n + 1) (m + 1) := ltb n m

infix ` <? `:50 := ltb

example : ¬ltb 2 2 := by simp
example : ltb 2 4 := by simp
example : ¬ltb 4 2 := by simp

/-
Theorem plus_O_n : ∀n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
-/

/- not sure how to get simp to do intro, so moved to the left -/
/- using our notation and simp only to avoid using zero_add -/
theorem plus_0_n (n : ℕ) : 0 +' n = n := by simp only [plus]

/-
Theorem plus_O_n' : ∀n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
-/

theorem plus_0_n' (n : ℕ) : 0 +' n = n := by refl

/-
Theorem plus_1_l : ∀n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : ∀n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
-/

theorem plus_1_l (n : ℕ) : 1 +' n = succ n := by simp
theorem mult_0_l (n : ℕ) : 0 *' n = 0 := by simp

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

example (n m : ℕ) (h : n = m) : n +' n = m +' m :=
  by simp *

/-
Theorem plus_id_exercise : ∀n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem plus_id (n m o : ℕ) (hnm : n = m) (hmo : m = o) :
  n +' m = m +' o := by simp *

/-
Theorem mult_0_plus : ∀n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite → plus_O_n.
  reflexivity. Qed.
-/

@[simp]
theorem mult_0_plus (n m : ℕ) : (0 +' n) *' m = n *' m :=
  by rw plus_0_n

/-
Theorem mult_S_1 : ∀n m : nat,
  m = S n →
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.
  (* (N.b. This proof can actually be completed with tactics other than
     rewrite, but please do use rewrite for the sake of the exercise.) *)
-/

open NatPlayground

theorem mult_S_1 (n m : ℕ) (h : m = succ n)
  : m *' (1 +' n) = m *' m := by simp *

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
theorem plus_1_neq_0_firsttry (n : ℕ) : (n +' 1) =? 0 = ff :=
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

@[simp]
theorem plus_1_neq_0 (n : ℕ) : (n +' 1) =? 0 = ff :=
  by cases n; simp

/-
Theorem negb_involutive : ∀b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.
-/

@[simp]
theorem negb_involutive (b : bool) : negb (negb b) = b :=
  by cases b; simp

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

@[simp]
theorem andb_commutative (b c : bool) : andb b c = andb c b :=
  by cases b; cases c; simp

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

theorem andb_commutative' (b c : bool) : andb b c = and c b :=
begin
cases b,
  { cases c,
    { refl },
    { refl } },
  { cases c, repeat { refl } }
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

/- bullets don't appear to be a thing in lean -/
@[simp]
theorem andb3_exchange (b c d : bool)
  : andb (andb b c) d = andb (andb b d) c :=
by cases b; cases c; cases d; refl

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
not sure if lean has anything like this
no point repeating previous definitions
-/

/-
Theorem andb_true_elim2 : ∀b c : bool,
  andb b c = true → c = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem andb_true_elim2 (b c : bool) (h : andb b c = tt)
  : c = tt :=
begin
  cases b,
    contradiction,
  simp at h,
  exact h
end

theorem andb_true_elim2' (b c : bool) (h : andb b c = tt)
  : c = tt :=
begin
  cases c,
    rwa [andb_commutative, andb] at h,
  refl,
end

/-
Theorem zero_nbeq_plus_1 : ∀n : nat,
  0 =? (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem zero_nbeq_plus_1 (n : ℕ) : 0 =? (n + 1) = ff :=
  by cases n; simp

/-
Theorem identity_fn_applied_twice :
  ∀(f : bool → bool),
  (∀(x : bool), f x = x) →
  ∀(b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem identity_fn_applied_twice
  (f : bool → bool)
  (h : ∀ x : bool, f x = x)
  (b : bool) : f (f b) = b := by simp *

@[simp]
theorem negation_fn_applied_twice
  (f : bool → bool)
  (h : ∀ x : bool, f x = negb x)
  (b : bool) : f (f b) = b :=
begin
  have : negb (negb b) = b, by cases b; simp,
  simp *
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
 "You will probably need both destruct and rewrite,
 but destructing everything in sight is not the best way."

 lean says lol
-/
theorem andb_eq_orb (b c : bool) (h : andb b c = orb b c)
  : b = c := by cases b; cases c; simp * at *

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

@[simp]
def incr : bin → bin
| Z := B Z
| (A b) := B b
| (B b) := A (incr b)

@[simp]
def bin_to_nat : bin → ℕ
| Z := 0
| (A b) := 2 * bin_to_nat b
| (B b) := 2 * bin_to_nat b + 1

@[simp]
def nat_to_bin : ℕ → bin
| 0 := Z
| (n + 1) := incr (nat_to_bin n)

example : bin_to_nat (nat_to_bin 127) = 127 := by refl
