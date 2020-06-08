/-
From LF Require Export Basics.
-/

import data.nat.basic
import .ch01_basics

/-
Theorem plus_n_O_firsttry : ∀n:nat,
  n = n + 0.
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.
-/

/- yeah, this would fail in coq -/
theorem plus_n_0 (n : ℕ) : n = n + 0 := by simp

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

/- still obviously works -/
theorem plus_n_0_secondtry (n : ℕ) : n = n + 0 :=
  by cases n; simp

/-
Theorem plus_n_O : ∀n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.
-/

/- plus_n_0 is part of core, which is why previous versions worked -/
theorem plus_n_0' (n : ℕ) : n = n + 0 :=
begin
  induction n with n ih,
    refl,
  rw ih
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

theorem minus_diag (n : ℕ) : n - n = 0 :=
  by induction n; simp *

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

open nat

/-
  n.b. lean defines mul with recursion on the right,
  which makes this too trivial
-/
@[simp]
theorem mult_0_r (n : ℕ) : n * 0 = 0 := rfl

/-
  defining other way to get similar challenge as expected
-/
@[simp]
theorem mult_succ (n m : ℕ) : n * succ m = (n * m) + n := rfl

@[simp]
theorem mult_n_0 (n : ℕ) : 0 * n = 0 :=
  by induction n; simp only [*, mult_0_r, mult_succ]

theorem plus_n_Sm (n m : ℕ) : succ (n + m) = n + succ m := rfl

@[simp]
theorem plus_Sn_m (n m : ℕ) : succ n + m = succ (n + m) :=
  by induction m; simp only [*, ←plus_n_Sm, add_zero]

/- this took a depressingly long time to write -/
theorem plus_comm (n m : ℕ) : n + m = m + n :=
  by induction n; induction m;
    simp only [*, plus_Sn_m, add_zero, zero_add]

/- need to prevent add_assoc from running -/
theorem plus_assoc (n m p : ℕ) : n + (m + p) = (n + m) + p :=
  by induction n; simp only [*, plus_Sn_m, zero_add]

/-
Fixpoint double (n:nat) :=
  match n with
  | O ⇒ O
  | S n' ⇒ S (S (double n'))
  end.
-/

@[simp]
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
  simp [*, ←plus_n_Sm]
end

/-
Theorem evenb_S : ∀n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem evenb_S (n : ℕ) : evenb (succ n) = negb (evenb n) :=
  by induction n; simp [*, evenb]

/-
Theorem mult_0_plus' : ∀n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite → H.
  reflexivity. Qed.
-/

theorem mult_0_plus' (n m : ℕ) : (0 + n) * m = n * m :=
begin
  have h : 0 + n = n, { simp },
  rewrite h
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

theorem plus_rearrange_firsttry (n m p q : ℕ)
  : (n + m) + (p + q) = (m + n) + (p + q) :=
begin
  rw plus_comm,
  /- simp is a bit smarter though -/
  simp [plus_comm]
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

theorem plus_rearrange (n m p q : ℕ)
  : (n + m) + (p + q) = (m + n) + (p + q) :=
begin
  have h : n + m = m + n,
    rw plus_comm,
  rw h,
end

/- or tell it where to apply -/
theorem plus_rearrange' (n m p q : ℕ)
  : (n + m) + (p + q) = (m + n) + (p + q) := by rw plus_comm n m

/-
Theorem plus_assoc' : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite → IHn'. reflexivity. Qed.
-/

/- fighting tactic differences is starting to suck -/
theorem plus_assoc' (n m p : ℕ) : n + (m + p) = (n + m) + p :=
begin
  induction n with n ih,
    repeat { rw zero_add },
  repeat { rw plus_Sn_m },
  rw ih
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
theorem plus_assoc'' (n m p : ℕ) : n + (m + p) = (n + m) + p :=
begin
  induction n,
    case zero {
      show 0 + (m + p) = (0 + m) + p,
      repeat { rw zero_add }
    },

  case succ : n' ih {
    show (succ n') + (m + p) = ((succ n') + m) + p,
    repeat {rw plus_Sn_m },
    show succ (n' + (m + p)) = succ ((n' + m) + p),
    rw ih
  }
end