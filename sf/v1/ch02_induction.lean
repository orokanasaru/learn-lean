/-
From LF Require Export Basics.
-/

import data.nat.basic
import tactic.basic
import .ch01_basics

open basics (evenb)
open nat (succ)

namespace induction

/-
Theorem plus_n_O_firsttry : ∀n:nat,
  n = n + 0.
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.
-/

/- swapping order as this is refl in lean -/

/- zero_add is a theorem used by simp in lean -/
theorem zero_add_firsttry (n : ℕ) : 0 + n = n := by squeeze_simp

/-
Theorem plus_n_O_secondtry : ∀n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.
-/

/- zero_add is still a theorem in lean -/
theorem zero_add_secondtry (n : ℕ) : 0 + n = n :=
begin
  cases n,
    refl,
  squeeze_simp,
end

/-
Theorem plus_n_O : ∀n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.
-/

theorem zero_add (n : ℕ) : 0 + n = n :=
begin
  induction n with n ih,
    refl,
  rw nat.add_succ,
  rw ih,
end

/-
Theorem minus_diag : ∀n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite → IHn'. reflexivity. Qed.
-/

theorem sub_self (n : ℕ) : n - n = 0 :=
begin
  induction n with n ih,
    refl,
  /- don't use version from library -/
  simp only [nat.succ_sub_succ_eq_sub],
  rw ih,
end

/-
Theorem mult_0_r : ∀n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem plus_n_Sm : ∀n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) Admitted.
Theorem plus_comm : ∀n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem plus_assoc : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
-/
/-
  n.b. lean defines mul with recursion on the right,
  which makes this too trivial
-/
theorem mul_zero (n : ℕ) : n * 0 = 0 := rfl

/-
  defining other way to get similar challenge as expected
-/
theorem mul_succ (n m : ℕ) : n * succ m = (n * m) + n := rfl

theorem zero_mul (n : ℕ) : 0 * n = 0 :=
begin
  induction n with n ih,
    refl,
  rw mul_succ,
  rw ih,
end

theorem add_succ (n m : ℕ) : n + succ m = succ (n + m) := rfl

theorem succ_add (n m : ℕ) : succ n + m = succ (n + m) :=
begin
  induction m with m ih,
    refl,
  rw add_succ,
  rw ih,
end

theorem add_comm (n m : ℕ) : n + m = m + n :=
begin
  induction n with n ih,
    rw add_zero,
    rw zero_add,
  rw add_succ,
  rw succ_add,
  rw ih,
end

theorem add_assoc (n m p : ℕ) : n + (m + p) = (n + m) + p :=
begin
  induction n with n ih,
    rw [zero_add, zero_add],
  rw [succ_add, succ_add, succ_add],
  rw ih,
end

/-
Fixpoint double (n:nat) :=
  match n with
  | O ⇒ O
  | S n' ⇒ S (S (double n'))
  end.
-/

def double : ℕ → ℕ
| 0 := 0
| (n + 1) := double n + 2

/-
Lemma double_plus : ∀n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma double_plus (n : ℕ) : double n = n + n :=
begin
  induction n with n ih,
    refl,
  rw double,
  rw ih,
  rw succ_add,
  rw [add_succ, add_succ, add_succ],
  rw add_zero,
end

/-
Theorem evenb_S : ∀n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem evenb_S (n : ℕ) : evenb (succ n) = bnot (evenb n) :=
begin
  induction n with n ih,
    refl,
  rw evenb,
  rw ih,
  rw bnot_bnot,
end

/-
Theorem mult_0_plus' : ∀n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite → H.
  reflexivity. Qed.
-/

theorem zero_add_mul' (n m : ℕ) : (0 + n) * m = n * m :=
begin
  have h : 0 + n = n, rw zero_add,
  rewrite h,
end

/-
Theorem plus_rearrange_firsttry : ∀n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite → plus_comm.
  (* Doesn't work...Coq rewrites the wrong plus! *)
Abort.
-/

theorem add_rearrange_firsttry (n m p q : ℕ)
  : (n + m) + (p + q) = (m + n) + (p + q) :=
begin
  rw add_comm,
  /- simp is a bit smarter though -/
  /- ac_refl also works -/
  simp [add_comm],
end

/-
Theorem plus_rearrange : ∀n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite → plus_comm. reflexivity. }
  rewrite → H. reflexivity. Qed.
-/

theorem add_rearrange (n m p q : ℕ)
  : (n + m) + (p + q) = (m + n) + (p + q) :=
begin
  have h : n + m = m + n,
    rw add_comm,
  rw h,
end

/- or tell it where to apply -/
theorem add_rearrange' (n m p q : ℕ)
  : (n + m) + (p + q) = (m + n) + (p + q) := by rw add_comm n m

/-
Theorem plus_assoc' : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite → IHn'. reflexivity. Qed.
-/

theorem add_assoc' (n m p : ℕ) : n + (m + p) = (n + m) + p :=
begin
  induction n with n ih,
    rw [zero_add, zero_add],
  rw [succ_add, succ_add, succ_add],
  rw ih,
end

/-
Theorem plus_assoc'' : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite → IHn'. reflexivity. Qed.
-/

/- we can do better -/
/- show / have are kind of strange -/
theorem add_assoc'' (n m p : ℕ) : n + (m + p) = (n + m) + p :=
begin
  induction n,
  case zero {
    show 0 + (m + p) = (0 + m) + p,
    rw [zero_add, zero_add],
  },
  case succ : n ih {
    show (succ n) + (m + p) = ((succ n) + m) + p,
    rw [succ_add, succ_add, succ_add],
    show succ (n + (m + p)) = succ ((n + m) + p),
    rw ih,
  }
end

end induction