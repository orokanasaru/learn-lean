import tactic.basic
import .ch02_induction
import .ch03_lists
import .ch04_poly

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

theorem silly1
  (n m o p : ℕ)
  (eq1 : n = m)
  (eq2 : [n, o] = [n, p]) : [n, o] = [m, p] :=
begin
  rw ←eq1,
  exact eq2
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

theorem silly2
  (n m o p : ℕ)
  (eq1 : n = m)
  (eq2 : ∀ q r : ℕ, q = r → [q, o] = [r, p]) : [n, o] = [m, p] :=
begin
  apply eq2,
  exact eq1
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

theorem silly2a
  (n m : ℕ)
  (eq1 : (n, n) = (m, m))
  (eq2 : ∀ q r : ℕ, (q, q) = (r, r) → [q] = [r]) : [n] = [m] :=
begin
  apply eq2,
  exact eq1
end

/-
Theorem silly_ex :
     (∀n, evenb n = true → oddb (S n) = true) →
     oddb 3 = true →
     evenb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

open nat

/-
  i have literally no idea why this works,
  or if this would work in the coq version
-/
theorem silly_ex
  (h : ∀ n, evenb n = tt → oddb (succ n) = tt)
  (v : oddb 3 = tt) : evenb 4 = tt := by apply v

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

theorem silly3_firsttry (n : ℕ) (h: tt = (n =? 5)) :
  succ (succ n) =? 7 = tt :=
begin
  symmetry,
  apply h
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

open poly

@[simp]
lemma rev_twice (l : lst ℕ) : rev (rev l) = l :=
by induction l; simp *

theorem rev_exercise1 (l l' : lst ℕ) (h: l = rev l') :
  l' = rev l := by simp [*, rev_twice]

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
  (eq2 : [c, d] = [e, f]) : [a, b] = [e, f] :=
begin
  rw eq1,
  rw eq2
end

/-
Theorem trans_eq : ∀(X:Type) (n m o : X),
  n = m → m = o → n = o.
Proof.
  intros X n m o eq1 eq2. rewrite → eq1. rewrite → eq2.
  reflexivity. Qed.
-/

theorem trans_eq
  {X : Type}
  (n m o : X)
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

example
  (a b c d e f : ℕ)
  (eq1 : [a, b] = [c, d])
  (eq2 : [c, d] = [e, f]) : [a, b] = [e, f] :=
begin
  apply trans_eq,
  /-
    don't see an equivalent notation
    applying eq1 solves the metavariable in lean
  -/
  apply eq1,
  apply eq2
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
  (n m o p : ℕ)
  (eq1 : m = minustwo o)
  (eq2 : n + p = m) : (n + p) = (minustwo o) :=
begin
  apply trans_eq,
  apply eq2,
  apply eq1
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

theorem S_injective (n m : ℕ) (h1 : succ n = succ m) : n = m :=
begin
  have h2 : n = pred (succ n), refl,
  rw h2,
  rw h1,
  refl -- why is this needed here and never before?
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

theorem S_injective' (n m : ℕ) (h : succ n = succ m) : n = m :=
  by injection h -- back to lean doing just a bit extra

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

theorem injection_ex1 (n m o : ℕ) (h : [n, m] = [o, o])
  : [n] = [m] :=
begin
  injection h with h1 h2,
  rw h1,
  rw h2
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

theorem injection_ex2 (n m : ℕ) (h : [n] = [m]) : n = m :=
  by injection h

/-
Example injection_ex3 : ∀(X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j →
  y :: l = x :: j →
  x = y.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem injection_ex3
  {X : Type} (x y z : X) (l j : list X)
  (eq1 : x :: y :: l = z :: j)
  (eq2 : y :: l = x :: j) : x = y :=
begin
  -- eq1 is useless, so are other injections from eq2
  injection eq2 with h1,
  rw h1
end

/-- lazier version -/
theorem injection_ex3'
  {X : Type} (x y z : X) (l j : list X)
  (eq1 : x :: y :: l = z :: j)
  (eq2 : y :: l = x :: j) : x = y :=
by injections; simp *

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

/- i think contradiction handles discriminate -/
theorem eqb_0_l (n : ℕ) (h: 0 =? n = tt) : n = 0 :=
begin
  cases n,
    refl,
  contradiction
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

theorem discriminate_ex1 (n : ℕ) (contra : succ n = 0)
  : 2 + 2 = 5 := by contradiction

theorem discriminate_ex2 (n m : ℕ) (h : ff = tt) : [n] = [m] :=
  by contradiction

/-
Example discriminate_ex3 :
  ∀(X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] →
    x = z.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example
  {X : Type}
  (x y z : X)
  (l j : list X)
  (h : x :: y :: l = []) : x = z := by contradiction

/-
Theorem S_inj : ∀(n m : nat) (b : bool),
     (S n) =? (S m) = b →
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.
-/

theorem S_inj (n m : ℕ) (b : bool) (h : succ n =? succ m = b)
  : n =? m = b := by simp at h; exact h

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

/- yeah, this does not appear to exist in lean -/
theorem silly3'
  (n : ℕ)
  (eq : n =? 5 = tt → succ (succ n) =? 7 = tt)
  (h : tt = (n =? 5)) : tt = (succ (succ n) =? 7) :=
begin
  have h : (n =? 5) = tt,
    symmetry,
    exact h,
  have h : succ (succ n) =? 7 = tt,
    rw eq h,
  have h : tt = (succ (succ n) =? 7),
    symmetry,
    exact h,
  rw h
end

/-
Theorem plus_n_n_injective : ∀n m,
     n + n = m + m →
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* FILL IN HERE *) Admitted.
-/

theorem plus_n_n_injective : ∀ (n m : ℕ), n + n = m + m → n = m :=
begin
  intro n,
  induction n with n ih,
    intro m,
    cases m,
      intro h,
      refl,
    contradiction,
  intro m,
  cases m,
    intro h,
    contradiction,
  intro h,
  simp [←plus_n_Sm] at h,
  simp [ih m h]
end

/-
  leaving for posterity
  this was way easier to write
-/
theorem plus_n_n_injective' : ∀ (n m : ℕ), n + n = m + m → n = m
| 0 0 := by intro; refl
| 0 (succ m) := by contradiction
| (succ n) 0 := by contradiction
| (succ n) (succ m) :=
begin
  intro h,
  simp [←plus_n_Sm] at h,
  simp [plus_n_n_injective n m h]
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

theorem double_injective_take2
  (n m : ℕ) (eq : double n = double m) : n = m :=
begin
  -- could also use revert before the induction
  -- and intros after
  induction m with m ih generalizing n eq,
    cases n,
      refl,
    contradiction,
  cases n,
    contradiction,
  simp,
  apply ih,
  injection eq with goal,
  injection goal
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

/- not sure if lean can do intro destruction like that -/
theorem eqb_id_true
  (x y : lists.Id) (h : lists.eqb_id x y = tt) : x = y :=
begin
  cases x with x,
  cases y with y,
  simp,
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
theorem nth_error_after_last {X : Type}
  (n : ℕ) (l : list X) (h : l.length = n) : l.nth n = none :=
begin
  induction n with n ih generalizing l h,
    cases l,
      refl,
    contradiction,
  cases l,
    contradiction,
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

/- may as well be cool here -/
def square {α : Type} [has_mul α] (n : α) := n * n

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

lemma square_mult (n m : ℕ)
  : square (n * m) = square n * square m :=
begin
  /- simp [square] would also work -/
  unfold square,
  -- mul_assoc seems to be a bit different
  repeat { rw ←mul_assoc },
  simp [mul_comm, mul_assoc],
end

namespace silly

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

  reflexivity will look at any def apparently
-/
lemma silly_fact_1 (m : ℕ) : foo m + 1 = foo (m + 1) + 1 :=
  rfl

local attribute [simp] foo

lemma silly_fact_1' (m : ℕ) : foo m + 1 = foo (m + 1) + 1 :=
  by simp

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

-- lemma silly_fact_2_FAILED (m : ℕ)
--   : bar m + 1 = bar (m + 1) + 1 :=
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

lemma silly_fact_2 (m : ℕ)
  : bar m + 1 = bar (m + 1) + 1 :=
by cases m; refl

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
not sure if unfold is better in coq, but it's not really
all that helpful here
-/
lemma silly_fact_2' (m : ℕ)
  : bar m + 1 = bar (m + 1) + 1 :=
begin
  unfold bar,
  cases m; refl,
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

/-- i think this is the first time i've written ite in lean -/
def sillyfun (n : ℕ) : bool :=
  if n =? 3 then ff
  else if n =? 5 then ff
  else ff

theorem sillyfun_false (n : ℕ) : sillyfun n = ff :=
by cases (n =? 3); cases (n =? 5); simp [sillyfun]

/-
Theorem combine_split : ∀X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) →
  combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
this works, but there's no way it's the expected solution
-/

@[simp]
lemma split_injective
  {α β : Type}
  {h : α * β} {t : lst (α * β)}
  {h₁ : α} {t₁ : lst α}
  {h₂ : β} {t₂ : lst β}
  (eq : split (h::t) = ⦃h₁::t₁, h₂::t₂⦄) :
  ⦃h₁, h₂⦄ = h ∧ split t = ⦃t₁, t₂⦄ :=
begin
  simp at eq,
  cases_type* and,
  have ht₁ : fst (split t) = t₁, simp *,
  have ht₂ : snd (split t) = t₂, simp *,
  constructor,
    cases h; simp * at *,
  cases (split t); simp * at *,
end

theorem combine_split {α β : Type} :
  ∀ (l : lst (α * β))
  (l₁ : lst α)
  (l₂ : lst β)
  (hs : split l = ⦃l₁, l₂⦄),
  combine l₁ l₂ = l
| ⟦⟧ ⟦⟧ ⟦⟧ := by simp
| (h::t) ⟦⟧ _ := by simp
| (h::t) _ ⟦⟧ := by simp
| ⟦⟧ (h₁::t₁) _ := by simp
| ⟦⟧ _ (h₂::t₂) := by simp
| (h::t) (h₁::t₁) (h₂::t₂) :=
begin
  intro hs,
  have : ⦃h₁, h₂⦄ = h ∧ split t = ⦃t₁, t₂⦄,
    exact split_injective hs,
  simp,
  exact ⟨this.left, combine_split t t₁ t₂ this.right⟩
end

/-
Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.
-/

def sillyfun1 (n : ℕ) : bool :=
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

-- theorem sillyfun1_odd_FAILED (n : ℕ) (eq : sillyfun1 n = tt)
--   : oddb n = tt :=
-- begin
--   unfold sillyfun1 at eq,
--   cases (n =? 3),
--   /- stuck -/
-- end

theorem sillyfun1_odd (n : ℕ) (eq : sillyfun1 n = tt)
  : oddb n = tt :=
begin
  unfold sillyfun1 at eq,
  cases heqe3 : (n =? 3),
    cases heqe5 : (n =? 5),
      simp * at *,
    have : n = 5, exact eqb_true n 5 heqe5,
    simp *,
  have : n = 3, exact eqb_true n 3 heqe3,
  simp *,
end

/-
Theorem bool_fn_applied_thrice :
  ∀(f : bool → bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem bool_fn_applied_thrice (f: bool → bool) (b: bool) :
  f (f (f b)) = f b :=
begin
  cases fb : f b,
    cases bb : b,
      rw bb at fb,
      repeat { rw fb },
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
  repeat { rw fb },
end

/-
Theorem eqb_sym : ∀(n m : nat),
  (n =? m) = (m =? n).
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem eqb_sym : ∀ n m : ℕ, (n =? m) = (m =? n)
| 0 0 := by simp
| 0 (m + 1) := by simp
| (n + 1) 0 := by simp
| (n + 1) (m + 1) := eqb_sym n m

/-
Theorem eqb_trans : ∀n m p,
  n =? m = true →
  m =? p = true →
  n =? p = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem eqb_trans : ∀ n m p : ℕ, n =? m = tt → m =? p = tt → n =? p = tt
| 0 0 0 := by simp
| 0 (m + 1) _ := by simp
| 0 0 (p + 1) := by simp
| _ (m + 1) 0 := by simp
| (n + 1) 0 _ := by simp
| (n + 1) (m + 1) (p + 1) := eqb_trans n m p


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
this is horrible
could try cleaning it up, but i'm confident that the approach is wrong
-/
@[simp]
lemma min_succ (m n : ℕ) : min (succ m) (succ n) = min m n + 1 :=
begin
  have : (m + 1) <= (n + 1) ↔ m <= n,
    constructor,
      exact le_of_succ_le_succ,
    exact succ_le_succ,
  cases nat.decidable_le m n; simp [*, min],
end

@[simp]
lemma combine_len {α β : Type} :
  ∀ (l₁ : lst α) (l₂ : lst β),
  length (combine l₁ l₂) = min (length l₁) (length l₂)
| ⟦⟧ ⟦⟧ := by simp
| (h::t) ⟦⟧ := by simp
| ⟦⟧ (h::t) := by simp
| (h₁::t₁) (h₂::t₂) := by simp [combine_len t₁ t₂]

theorem split_combine {α β : Type} :
  ∀ (l : lst (α * β))
  (l₁ : lst α)
  (l₂ : lst β)
  (hc : combine l₁ l₂ = l)
  (hl : length l₁ = length l₂),
  split l = ⦃l₁, l₂⦄
| ⟦⟧ ⟦⟧ ⟦⟧ := by simp
| (h::t) ⟦⟧ l₂ :=
begin
  intros,
  have : length (h::t) = 0,
    simp [←hc],
  contradiction,
end
| (h::t) l₁ ⟦⟧ :=
begin
  intros,
  have : length (h::t) = 0,
    simp [←hc],
  contradiction,
end
| ⟦⟧ (h₁::t₁) l₂ :=
begin
  intros,
  have hc₁ : length (combine (h₁::t₁) l₂) = length (⟦⟧),
    exact congr_arg length hc,
  have hc₂ : length (combine (h₁::t₁) l₂) = length (h₁::t₁),
    rw combine_len (h₁::t₁) l₂,
    simp *,
  rw hc₂ at hc₁,
  contradiction,
end
| ⟦⟧ l₁ (h₂::t₂) :=
begin
  intros,
  have hc₁ : length (combine l₁ (h₂::t₂)) = length (⟦⟧),
    exact congr_arg length hc,
  have hc₂ : length (combine l₁ (h₂::t₂)) = length (h₂::t₂),
    rw combine_len l₁ (h₂::t₂),
    simp *,
  rw hc₂ at hc₁,
  contradiction,
end
| (h::t) (h₁::t₁) (h₂::t₂) :=
begin
  intros,
  simp,
  simp at hc,
  have hl : length t₁ = length t₂,
    injection hl,
  repeat { constructor },
        simp [←hc.left],
      show fst (split t) = t₁,
      simp [split_combine t t₁ t₂ hc.right hl],
    simp [←hc.left],
  show snd (split t) = t₂,
  simp [split_combine t t₁ t₂ hc.right hl],
end

/-
Theorem filter_exercise : ∀(X : Type) (test : X → bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf →
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- this was so easy, wth -/

theorem filter_exercise {α : Type} (test : α → bool) (a : α) :
  ∀ (l lf : list α) (eq : filter test l = a :: lf), test a = tt
| [] := by intros; simp * at *
| (h::t) :=
begin
  intros,
  cases th : test h; simp [th] at eq,
    exact filter_exercise t lf eq,
  rw ←eq.left,
  exact th,
end

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

@[simp]
def forallb {α : Type} (p : α → bool) : list α → bool
| [] := tt
| (h::t) := if p h then forallb t else ff

example : forallb oddb [1,3,5,7,9] := rfl

example : forallb negb [ff,ff] := rfl

example : forallb evenb [0,2,4,5] = ff := rfl

example : forallb (eqb 5) [] := rfl

@[simp]
def existsb {α : Type} (p : α → bool) : list α → bool
| [] := ff
| (h::t) := if p h then tt else existsb t

example : existsb (eqb 5) [0,2,4,6] = ff := rfl

example : existsb (andb tt) [tt,tt,ff] := rfl

example : existsb oddb [1,0,0,0,0,3] := rfl

example : existsb evenb [] = ff := rfl

/- serious issues if using not forallb -/

@[simp]
def existsb' {α : Type} (p : α → bool) (l : list α) : bool :=
  if forallb (λ a, not $ p a) l then ff else tt

/- serious issues if using equation compiler -/

theorem existsb_existsb' {α : Type} (p : α → bool) (l : list α)
  : existsb p l = existsb' p l :=
begin
  induction l with h t ih,
    simp,
  cases ph : p h; simp [ph],
  simp at ih,
  exact ih,
end