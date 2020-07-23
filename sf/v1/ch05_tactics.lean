import tactic.basic
import .ch02_induction
import .ch03_lists
import .ch04_poly

open nat (
  succ add_one add_succ succ_add le_of_succ_le_succ succ_le_succ
  decidable_le
)

open basics (evenb oddb sub_two eqb)
open induction (double)
open lists (eqb_id)
open poly (split combine)
open poly.list (length filter)

local infix ` =? `:50 := eqb

variables {α β γ : Type}
variables (b : bool)
variables (n m o p : ℕ)

namespace tactics

/-
Theorem silly1 : ∀(n m o p : nat),
     n = m →
     [n;o] = [n;p] →
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.
-/

theorem silly₁ (eq₁ : n = m) (eq₂ : [n, o] = [n, p])
  : [n, o] = [m, p] :=
begin
  rw ←eq₁,
  apply eq₂,
end

/-
Theorem silly2 : ∀(n m o p : nat),
     n = m →
     (∀(q r : nat), q = r → [q;o] = [r;p]) →
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.
-/

theorem silly₂
  (eq₁ : n = m)
  (eq₂ : ∀ q r : ℕ, q = r → [q, o] = [r, p])
  : [n, o] = [m, p] :=
begin
  apply eq₂,
  apply eq₁,
end

/-
Theorem silly2a : ∀(n m : nat),
     (n,n) = (m,m) →
     (∀(q r : nat), (q,q) = (r,r) → [q] = [r]) →
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.
-/

theorem silly₂a
  (eq₁ : (n, n) = (m, m))
  (eq₂ : ∀ q r : ℕ, (q, q) = (r, r) → [q] = [r]) : [n] = [m] :=
begin
  apply eq₂,
  apply eq₁,
end

/-
Theorem silly_ex :
     (∀n, evenb n = true → oddb (S n) = true) →
     oddb 3 = true →
     evenb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem silly_ex
  (h : evenb n = tt → oddb n.succ = tt)
  (v : oddb 3 = tt)
  : evenb 4 = tt := rfl

/-
Theorem silly3_firsttry : ∀(n : nat),
     true = (n =? 5) →
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H. Qed.
-/

theorem silly₃_firsttry (h: tt = (n =? 5)) :
  n.succ.succ =? 7 = tt :=
begin
  symmetry,
  apply h,
end

/-
Theorem rev_exercise1 : ∀(l l' : list nat),
     l = rev l' →
     l' = rev l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
  also, lean doesn't appear to have any relevant lemmas
-/

/-
using poly.list as we already proved the relevant lemma,
and doing this with the library version is unpleasant,
and unnecessary given the goal of this exercise
-/
theorem rev_exercise₁ (l l' : poly.list ℕ) (h: l = l'.reverse)
  : l' = l.reverse :=
begin
  rw h,
  symmetry,
  apply poly.reverse_involutive,
end

/-
Example trans_eq_example : ∀(a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite → eq1. rewrite → eq2. reflexivity. Qed.
-/

example
  (a b c d e f : ℕ)
  (eq1 : [a, b] = [c, d])
  (eq2 : [c, d] = [e, f])
  : [a, b] = [e, f] :=
begin
  rw eq1,
  rw eq2,
end

/-
Theorem trans_eq : ∀(X:Type) (n m o : X),
  n = m → m = o → n = o.
Proof.
  intros X n m o eq1 eq2. rewrite → eq1. rewrite → eq2.
  reflexivity. Qed.
-/

theorem eq.trans
  (n m o : α)
  (eq1 : n = m)
  (eq2 : m = o) : n = o := by rw [eq1, eq2]

/-
Example trans_eq_example' : ∀(a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.
-/

/-
TODO: figure out if there's similar notation
      applying eq1 solves the metavariable in lean
-/
example
  (a b c d e f : ℕ)
  (eq₁ : [a, b] = [c, d])
  (eq₂ : [c, d] = [e, f]) : [a, b] = [e, f] :=
begin
  apply eq.trans,
  apply eq₁,
  apply eq₂,
end

/-
Example trans_eq_exercise : ∀(n m o p : nat),
     m = (minustwo o) →
     (n + p) = m →
     (n + p) = (minustwo o).
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- no clue why this is 3 stars-/
example
  (eq₁ : m = sub_two o)
  (eq₂ : n + p = m) : (n + p) = (sub_two o) :=
begin
  apply eq.trans,
  apply eq₂,
  apply eq₁,
end

/-
Theorem S_injective : ∀(n m : nat),
  S n = S m →
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.
-/

/-
TODO: is there a rw that's better at finishing?
-/
theorem succ_inj (h₁ : n.succ = m.succ) : n = m :=
begin
  have h₂ : n = n.succ.pred, refl,
  rw h₂,
  rw h₁,
  refl,
end

/-
Theorem S_injective' : ∀(n m : nat),
  S n = S m →
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.
-/

/- back to lean doing just a bit extra -/
theorem succ_inj' (h : n.succ = m.succ) : n = m := by injection h

/-
Theorem injection_ex1 : ∀(n m o : nat),
  [n; m] = [o; o] →
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
-/

theorem injection_ex₁ (h : [n, m] = [o, o]) : [n] = [m] :=
begin
  injection h with h₁ h₂,
  rw h₁,
  rw h₂,
end

/-
Theorem injection_ex2 : ∀(n m : nat),
  [n] = [m] →
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. rewrite Hnm.
  reflexivity. Qed.
-/

theorem injection_ex₂ (h : [n] = [m]) : n = m := by injection h

/-
Example injection_ex3 : ∀(X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j →
  y :: l = x :: j →
  x = y.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem injection_ex₃
  (x y z : α) (l j : list α)
  (eq₁ : x :: y :: l = z :: j)
  (eq₂ : y :: l = x :: j) : x = y :=
begin
  injection eq₂ with h₁ h₂,
  rw h₁,
end

/-
Theorem eqb_0_l : ∀n,
   0 =? n = true → n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl.
    intros H. discriminate H.
Qed.
-/

/-
not the last time cases will subsume another tactic
TODO: check earlier usages of cases to see if i already used it like this
-/

theorem eqb_0_l (h: 0 =? n = tt) : n = 0 :=
begin
  cases n,
    refl,
  cases h,
end

/-
Theorem discriminate_ex1 : ∀(n : nat),
  S n = O →
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : ∀(n m : nat),
  false = true →
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.
-/

theorem discriminate_ex₁ (h : n.succ = 0) : 2 + 2 = 5 := by cases h

theorem discriminate_ex₂ (n m : ℕ) (h : ff = tt) : [n] = [m] := by cases h

/-
Example discriminate_ex3 :
  ∀(X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] →
    x = z.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example (x y z : α) (l j : list α) (h : x :: y :: l = []) : x = z := by cases h

/-
Theorem S_inj : ∀(n m : nat) (b : bool),
     (S n) =? (S m) = b →
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.
-/

/-
this is the first place with in/at?!?!?!
(and i don't even use it here)
-/
theorem succ_injb (h : n.succ =? m.succ = b) : n =? m = b := by apply h

/-
Theorem silly3' : ∀(n : nat),
  (n =? 5 = true → (S (S n)) =? 7 = true) →
  true = (n =? 5) →
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.
-/

/-
lean doesn't have symmetry at or apply at.
let's learn replace and specialize instead
-/
theorem silly₃'
  (heq : n =? 5 = tt → n.succ.succ =? 7 = tt)
  (h : tt = (n =? 5)) : tt = (n.succ.succ =? 7) :=
begin
  replace h, exact eq.symm h,
  specialize heq h,
  replace h, exact eq.symm h,
  apply h,
end

/-
Theorem plus_n_n_injective : ∀n m,
     n + n = m + m →
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* FILL IN HERE *) Admitted.
-/

/- in library as bit0_inj -/
theorem add_self_inj : ∀{n m : ℕ}, n + n = m + m → n = m :=
begin
  intro n,
  induction n with n ih,
    intro m,
    cases m,
      intro h,
      refl,
    intro h,
    cases h,
  intro m,
  cases m,
    intro h,
    cases h,
  intro h,
  rw [succ_add, succ_add, add_succ, add_succ] at h,
  injection h with h,
  injection h with h,
  rw ih h,
end

/-
  leaving for posterity
  this was way easier to write
-/
theorem add_self_inj' : ∀{n m : ℕ}, n + n = m + m → n = m
| 0 0 := by intro; refl
| 0 (m + 1) := by contradiction
| (n + 1) 0 := by contradiction
| (n + 1) (m + 1) :=
begin
  intro h,
  simp only [add_succ, succ_add, add_zero] at h,
  rw add_self_inj' h,
end

/- this section really really needs to come before the last problem -/

/-
Theorem double_injective_FAILED : ∀n m,
     double n = double m →
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.
-/

-- theorem double_injective_FAILED
--   (n m : ℕ) : double n = m → n = m :=
-- begin
--   induction n with n ihn,
--     simp,
--     intro eq,
--     cases m,
--       refl,
--     contradiction,
--   intro eq,
--   cases m,
--     contradiction,
--   apply congr_arg, /- coq's f_equal -/
--   -- abort --
-- end

/-
Theorem double_injective : ∀n m,
     double n = double m →
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *) simpl.
      discriminate eq.
    + (* m = S m' *)
      apply f_equal.
      apply IHn'. injection eq as goal. apply goal. Qed.
-/

theorem double_injective (n m : ℕ)
  : double n = double m → n = m :=
begin
  -- gains nothing over having the nats on the right
  -- and using intro n, but what the heck
  revert m,
  induction n with n ihn,
    intros m eq,
    cases m,
      refl,
    contradiction,
  intros m eq,
  cases m,
    contradiction,
  apply congr_arg,
  apply ihn,
  injection eq with goal,
  injection goal
end

/-
Theorem eqb_true : ∀n m,
    n =? m = true → n = m.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem eqb_true : ∀ n m : ℕ, n =? m = tt → n = m :=
begin
  intro n,
  induction n with n ih,
    intros m eq,
    cases m,
      refl,
    contradiction,
  intros m eq,
  cases m,
    contradiction,
  simp at *,
  apply ih,
  exact eq
end

/-
Theorem double_injective_take2_FAILED : ∀n m,
     double n = double m →
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.
-/

-- theorem double_injective_take2_FAILED
--   (n m : ℕ) : double n = double m → n = m :=
-- begin
--   induction m,
--     simp,
--     intro eq,
--     cases n,
--       refl,
--     contradiction,
--   intro eq,
--   cases n,
--     contradiction,
--   apply congr_arg,
--   /- abort -/
-- end

/-
Theorem double_injective_take2 : ∀n m,
     double n = double m →
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.
-/

theorem double_injective_take₂ (eq : double n = double m) : n = m :=
begin
  -- could also use revert before the induction
  -- and intros after
  induction m with m ih generalizing n eq,
    cases n,
      refl,
    cases eq,
  cases n,
    cases eq,
  simp,
  apply ih,
  injection eq with goal,
  injection goal,
end

/-
Theorem eqb_id_true : ∀x y,
  eqb_id x y = true → x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.
-/

/-
congr is like injection but for the goal
-/

theorem eqb_id_true : ∀x y, eqb_id x y = tt → x = y :=
begin
  rintro ⟨m⟩ ⟨n⟩ h,
  congr,
  apply eqb_true,
  apply h,
end

/-
Theorem nth_error_after_last: ∀(n : nat) (X : Type) (l : list X),
     length l = n →
     nth_error l n = None.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- lean's nth should be the same as coq's nth_error -/
theorem nth_error_after_last (l : list α) (h : l.length = n) : l.nth n = none :=
begin
  induction n with n ih generalizing l h,
    cases l with a l,
      refl,
    cases h,
  cases l with a l,
    cases h,
  apply ih,
  injection h,
end

/-
Definition square n := n * n.

Lemma square_mult : ∀n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.
-/

/-
TODO: figure out best place to introduce typeclass stuff
-/
def square [has_mul α] (n : α) := n * n

/-
Lemma square_mult : ∀n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.
-/

/-
TODO: i've been using rw for this. should i use dsimp earlier?
TODO: figure out if this is the right spot to intro calc
TODO: find the right place to intro conv
-/
lemma square_mult : square (n * m) = square n * square m :=
begin
  unfold square,
  exact calc
    n * m * (n * m) = n * (m * n * m) : by rw [mul_assoc, mul_assoc]
    ...             = n * (n * m * m) : by rw mul_comm n m
    ...             = n * n * m * m   : by rw [←mul_assoc, ←mul_assoc]
    ...             = n * n * (m * m) : by rw mul_assoc,
end

/-
Definition foo (x: nat) := 5.
-/

def foo (x : ℕ) := 5

/-
Fact silly_fact_1 : ∀m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.
-/

/-
  this is not at all true in lean.
  lean requires either a simp attribute
  or explicitly adding as an arg to simp

  reflexivity is much more aggressive
-/
lemma silly_fact_1 : foo m + 1 = foo (m + 1) + 1 := rfl

section silly

local attribute [simp] foo

lemma silly_fact_1' : foo m + 1 = foo (m + 1) + 1 := by simp

end silly

/-
Definition bar x :=
  match x with
  | O ⇒ 5
  | S _ ⇒ 5
  end.
-/

/--
unfold and simp have serious issues with placeholders
instead of explicit constructors
refl has no such problem
if lean 3 wasn't dead, i'd be filing an issue
-/
def bar : ℕ → ℕ
| 0 := 5
| (succ _) := 5

/-
Fact silly_fact_2_FAILED : ∀m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.
-/

-- lemma silly_fact_2_FAILED : bar m + 1 = bar (m + 1) + 1 :=
-- begin
--   simp [bar],
-- end

/-
Fact silly_fact_2 : ∀m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
-/

lemma silly_fact_2 : bar m + 1 = bar (m + 1) + 1 :=
begin
  cases m,
    refl,
  refl,
end

/-
Fact silly_fact_2' : ∀m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
-/

/-
unfold in lean doesn't unfold to a match statement
-/
lemma silly_fact_2' : bar m + 1 = bar (m + 1) + 1 :=
begin
  unfold bar,
  cases m,
    refl,
  refl,
end

/-
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : ∀(n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.
-/

def sillyfun : bool :=
  if n =? 3 then ff
  else if n =? 5 then ff
  else ff

theorem sillyfun_false : sillyfun n = ff :=
begin
  unfold sillyfun,
  cases n =? 3,
  case tt : { refl }, /- messing around to reduce nesting -/
  cases n =? 5,
    refl,
  refl,
end

/-
Theorem combine_split : ∀X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) →
  combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
TODO: look for something simpler
-/

section split

/-
using poly.list and notation since that's what split
and combine were defined with
-/
local notation `[]` := poly.list.nil
local infix :: := poly.list.cons
local notation {x, y} := poly.prod.mk x y
local infix × := poly.prod

/-
injections is a recursive injection at all hypotheses
changes is show for hypotheses
-/
lemma split_injective
  {h : α × β} {t h₁ t₁ h₂ t₂}
  (eq : split (h :: t) = {h₁::t₁, h₂::t₂}) :
  {h₁, h₂} = h ∧ split t = {t₁, t₂} :=
begin
  rw split at eq,
  injections with eq₁ eq₂ eq₃ eq₄ eq₅ eq₆,
  change (split t).fst = t₁ at eq₄,
  change (split t).snd = t₂ at eq₆,
  cases h with h₁' h₂',
  constructor,
    rw [←eq₃, ←eq₅],
  cases (split t) with t₁' t₂',
  cases eq₄,
  cases eq₆,
  refl,
end

theorem combine_split :
  ∀{l : poly.list (α × β)} {l₁ l₂} (hs : split l = {l₁, l₂}),
  combine l₁ l₂ = l
| [] [] [] hs := rfl
| (h :: t) [] _ hs := by cases hs
| (h :: t) _ [] hs := by cases hs
| [] (h₁::t₁) _ hs := by cases hs
| [] _ (h₂::t₂) hs := by cases hs
| (h :: t) (h₁::t₁) (h₂::t₂) hs :=
begin
  have, exact split_injective hs,
  rw combine,
  congr,
    exact this.left,
  exact combine_split this.right,
end

end split

/-
Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.
-/

def sillyfun₁ : bool :=
  if n =? 3 then tt
  else if n =? 5 then tt
  else ff

/-
Theorem sillyfun1_odd_FAILED : ∀(n : nat),
     sillyfun1 n = true →
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.
-/

-- theorem sillyfun₁_odd_FAILED (eq : sillyfun₁ n = tt) : oddb n = tt :=
-- begin
--   unfold sillyfun₁ at eq,
--   cases (n =? 3),
--   /- stuck -/
-- end
/-
Theorem sillyfun1_odd : ∀(n : nat),
     sillyfun1 n = true →
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite → Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        eqn: again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite → Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq. Qed.
-/

/- lean's case equation does less rewriting than coq's -/
theorem sillyfun₁_odd (eq : sillyfun₁ n = tt) : oddb n = tt :=
begin
  unfold sillyfun₁ at eq,
  cases heqe3 : (n =? 3),
    rw heqe3 at eq,
    cases heqe5 : (n =? 5),
      rw heqe5 at eq,
      cases eq,
    rw eqb_true n 5 heqe5,
    refl,
  rw eqb_true n 3 heqe3,
  refl,
end

/-
Theorem bool_fn_applied_thrice :
  ∀(f : bool → bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem bool_fn_applied_thrice (f: bool → bool) : f (f (f b)) = f b :=
begin
  cases fb : f b,
    cases bb : b,
      rw bb at fb,
      rw [fb, fb],
    cases ff : f ff,
      exact ff,
    rw bb at fb,
    exact fb,
  cases bb : b,
    cases ft : f tt,
      rw bb at fb,
      exact fb,
    exact ft,
  rw bb at fb,
  rw [fb, fb],
end

/-
Theorem eqb_sym : ∀(n m : nat),
  (n =? m) = (m =? n).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem eqb_sym : ∀n m : ℕ, (n =? m) = (m =? n)
| 0 0 := rfl
| 0 (m + 1) := rfl
| (n + 1) 0 := rfl
| (n + 1) (m + 1) := eqb_sym n m

/-
Theorem eqb_trans : ∀n m p,
  n =? m = true →
  m =? p = true →
  n =? p = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem eqb_trans : ∀n m p : ℕ, n =? m = tt → m =? p = tt → n =? p = tt
| 0 0 0 hn hm := rfl
| 0 (m + 1) _ hn hm := by cases hn
| (n + 1) 0 _ hn hm := by cases hn
| _ 0 (p + 1) hn hm := by cases hm
| _ (m + 1) 0 hn hm := by cases hm
| (n + 1) (m + 1) (p + 1) hn hm := eqb_trans n m p hn hm


/-
Definition split_combine_statement : Prop
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.
-/

/-
TODO: this is horrible
could try cleaning it up, but i'm confident that the approach is wrong
-/

section poly

/-
using poly.list and notation since that's what split
and combine were defined with
-/
local notation `[]` := poly.list.nil
local infix :: := poly.list.cons
local notation {x, y} := poly.prod.mk x y
local infix × := poly.prod

lemma min_succ : min (succ m) (succ n) = min m n + 1 :=
begin
  have : (succ m) ≤ (succ n) ↔ m ≤ n,
    constructor,
      exact le_of_succ_le_succ,
    exact succ_le_succ,
  rw [min, min],
  simp only [this], /- no idea why i can't rw this -/
  cases decidable_le m n,
    simp only [h], /- also not sure how to plug this in -/
    rw [if_false, if_false],
  simp only [h],
  rw [if_true, if_true],
end

lemma combine_len  :
  ∀(l₁ : poly.list α) (l₂ : poly.list β),
  (combine l₁ l₂).length = min l₁.length l₂.length
| [] [] := rfl
| (h :: t) [] := rfl
| [] (h :: t) := rfl
| (h₁::t₁) (h₂::t₂) :=
begin
  unfold combine length,
  rw min_succ,
  congr,
  exact combine_len t₁ t₂,
end

theorem split_combine :
  ∀{l : poly.list (α × β)} {l₁ l₂}
  (hc : combine l₁ l₂ = l)
  (hl : l₁.length = l₂.length),
  split l = {l₁, l₂}
| [] [] [] hc hl := rfl
| (h :: t) [] l₂ hc hl := by cases hc
| (h :: t) (h₁::t₁) [] hc hl := by cases hc
| [] (h₁::t₁) l₂ hc hl :=
begin
  replace hc, exact congr_arg length hc,
  have hc' : (combine (h₁::t₁) l₂).length = (h₁::t₁).length,
    rw combine_len (h₁::t₁) l₂,
    rw ←hl,
    rw min_self,
  rw hc' at hc,
  cases hc,
end
| [] l₁ (h₂::t₂) hc hl :=
begin
  replace hc, exact congr_arg length hc,
  have hc' : (combine l₁ (h₂::t₂)).length = (h₂::t₂).length,
    rw combine_len l₁ (h₂::t₂),
    rw ←hl,
    rw min_self,
  rw hc' at hc,
  cases hc,
end
| (h :: t) (h₁::t₁) (h₂::t₂) hc hl :=
begin
  injection hl with hl,
  simp only [combine] at hc,
  unfold split,
  congr,
        rw ←hc.left,
      show (split t).fst = t₁,
      rw split_combine hc.right hl,
    rw ←hc.left,
  show (split t).snd = t₂,
  rw split_combine hc.right hl,
end

/-
Theorem filter_exercise : ∀(X : Type) (test : X → bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf →
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem filter_exercise {test} {a : α} :
  ∀{l lf} (eq : filter test l = a :: lf), test a = tt
| [] :=
begin
  intros,
  cases eq,
end
| (h :: t) :=
begin
  intros,
  rw filter at eq,
  cases th : test h,
    simp only [th, bool.coe_sort_ff, if_false] at eq,
    exact filter_exercise eq,
  simp only [th, bool.coe_sort_tt, if_true] at eq,
  rwa eq.left at th,
end

end poly

/-
Fixpoint forallb {X : Type} (test : X → bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. (* FILL IN HERE *) Admitted.

Fixpoint existsb {X : Type} (test : X → bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_4 : existsb evenb [] = false.
Proof. (* FILL IN HERE *) Admitted.

Definition existsb' {X : Type} (test : X → bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem existsb_existsb' : ∀(X : Type) (test : X → bool) (l : list X),
  existsb test l = existsb' test l.
Proof. (* FILL IN HERE *) Admitted.
-/

def all : list α → (α → bool) → bool
| [] p := tt
| (h :: t) p := if p h then all t p else ff

example : all [1, 3, 5, 7, 9] oddb := rfl

example : all [ff, ff] bnot := rfl

example : all [0, 2, 4, 5] evenb = ff := rfl

example : all [] (eqb 5) := rfl

def any : list α → (α → bool) → bool
| [] p := ff
| (h :: t) p := if p h then tt else any t p

example : any [0, 2, 4, 6] (eqb 5) = ff := rfl

example : any [tt, tt, ff] (band tt) := rfl

example : any [1, 0, 0, 0, 0, 3] oddb := rfl

example : any [] evenb = ff := rfl

def any' (l : list α) (p : α → bool) : bool := bnot $ all l (bnot ∘ p)

theorem existsb_existsb' (p) (l : list α) : any l p = any' l p :=
begin
  induction l with a l ih,
    refl,
  cases pa : p a,
    simp only [any, any', all, function.comp_app],
    simp only [pa],
    simp only [
      bool.coe_sort_ff, bool.bnot_false, if_false, if_true, bool.coe_sort_tt
    ],
    exact ih,
  simp only [any, any', all, function.comp_app],
  simp only [pa],
  simp only [
    bool.coe_sort_ff, bool.bnot_false, if_false, if_true,
    bool.coe_sort_tt, bool.bnot_true
  ],
end

end tactics
