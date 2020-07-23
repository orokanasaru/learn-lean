import tactic.basic
import tactic.linarith
import tactic.omega
import .ch06_logic

open nat (add_succ succ_add)
open list (
  filter nil_append append_nil foldr cons_append
  append_assoc length_append ne_nil_of_length_pos
)

open basics (leb eqb)
open induction (double double_add)
open logic (In in_app_iff eqb_eq eqb_neq)

local infix ` =? `:50 := eqb
local infix ` ≤? `:50 := leb

variables {α β γ : Type}
variables {P Q : Prop}
variables {a : α}
variables {n m o p : ℕ}

namespace indprop

/-
Inductive even : nat → Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).
-/

inductive even : ℕ → Prop
| ev_0 : even 0
| ev_ss {n} (h : even n) : even (n + 2)

open even

/-
Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n → wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "wrong_ev" must have "n"
        as 1st argument in "wrong_ev 0". *)
-/

-- inductive wrong_ev (n : ℕ) : Prop
-- | wrong_ev_0 : wrong_ev 0
-- | wrong_ev_ss : wrong_ev n → wrong_ev (succ (succ n))

/-
  Inductive even : nat → Prop :=
  | ev_0 : even 0
  | ev_SS : ∀n, even n → even (S (S n)).
-/

inductive even'' : ℕ → Prop
| ev_0 : even'' 0
| ev_ss : ∀n, even'' n → even'' (n + 2)

/-
Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.
-/

theorem even_four : even 4 :=
begin
  apply ev_ss,
  apply ev_ss,
  exact ev_0,
end

/-
Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.
-/

theorem even_four' : even 4 := ev_ss $ ev_ss ev_0

/-
Theorem ev_plus4 : ∀n, even n → even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.
-/

theorem even_add_four (h : even n) : even (n + 4) :=
begin
  apply ev_ss,
  apply ev_ss,
  exact h,
end

/-
Theorem ev_double : ∀n,
  even (double n).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem even_double : even (double n) :=
begin
  induction n with n ih,
    apply ev_0,
  apply ev_ss,
  exact ih,
end

/-
Theorem ev_inversion :
  ∀(n : nat), even n →
    (n = 0) ∨ (∃n', n = S (S n') ∧ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. ∃n'. split. reflexivity. apply E'.
Qed.
-/

theorem even_inv (e : even n) : (n = 0) ∨ (∃n', n = n' + 2 ∧ even n') :=
begin
  cases e with n' e',
    left,
    refl,
  right,
  use n',
  split,
    refl,
  apply e',
end

/-
Theorem ev_minus2 : ∀n,
  even n → even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.
-/

theorem even_sub_two (e : even n) : even (n - 2) :=
begin
  cases e with n' e',
    exact e,
  exact e',
end

/-
Theorem evSS_ev : ∀n,
  even (S (S n)) → even n.
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that n is even from no assumptions! *)
Abort.
-/

-- theorem evss_ev (h : even (n + 2)) : even n :=
-- begin
--   destruct h,
--   sorry,
-- end

/-
Theorem evSS_ev : ∀n, even (S (S n)) → even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.
-/

theorem add_two_even (e : even (n + 2)) : even n :=
begin
  replace e, exact even_inv e,
  rcases e with ⟨⟨⟩⟩ | ⟨n', hn, he⟩,
  injections with hn' heq,
  rwa heq,
end

/-
Theorem evSS_ev' : ∀n,
  even (S (S n)) → even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.
-/

theorem add_two_even' (e : even (n + 2)) : even n :=
begin
  cases e with _ e',
  exact e',
end

/-
Theorem one_not_even : ¬even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ¬even 1.
  intros H. inversion H. Qed.
-/

/-
TODO: see if this is the right time to introduce by_contra
as a slightly more readable version of intro for negated statements
-/
theorem one_not_even : ¬even 1 :=
begin
  by_contra h,
  replace h, exact even_inv h,
  rcases h with ⟨⟨⟩⟩ | ⟨_, ⟨⟩, _⟩,
end

theorem one_not_even' : ¬even 1 := by rintro ⟨⟩

/-
Theorem SSSSev__even : ∀n,
  even (S (S (S (S n)))) → even n.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem add_four_even (h : even (n + 4)) : even n :=
begin
  apply add_two_even,
  apply add_two_even,
  exact h,
end

/-
Theorem even5_nonsense :
  even 5 → 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem even5_nonsense (h : even 5) : 2 + 2 = 9 :=
begin
  replace h, exact add_four_even h,
  cases h,
end

/-
TODO: go back to tactics and use destruct?
-/

/-
Theorem inversion_ex1 : ∀(n m o : nat),
  [n; m] = [o; o] →
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : ∀(n : nat),
  S n = O →
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.
-/

/- cases does not do injection in lean -/

theorem inversion_ex₁ (h : [n, m] = [o, o]) : [n] = [m] :=
begin
  cases h,
  injection h,
end

theorem inversion_ex₂ (h : n + 1 = 0) : 2 + 2 = 5 := by cases h

/- Lemma ev_even_firsttry : ∀n,
  even n → ∃k, n = double k.
Proof.
(* WORKED IN CLASS *)
 intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    ∃0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.
    assert (I : (∃k', n' = double k') →
                (∃k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. ∃(S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)
Abort.
-/

-- lemma ev_even_firstry (e : even n): ∃k, n = double k :=
-- begin
--   cases e with n' e',
--     exact ⟨0, rfl⟩,
--   have i : (∃k', n' = double k') → (∃k, n' + 2 = double k),
--     rintro ⟨k', hk'⟩,
--     rw hk',
--     exact ⟨k' + 1, rfl⟩,
--   sorry,
-- end

/-
Lemma ev_even : ∀n,
  even n → ∃k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    ∃0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. ∃(S k'). reflexivity.
Qed.
-/

lemma even_even (e : even n) : ∃k, n = double k :=
begin
  induction e with n' e' ih,
    exact ⟨0, rfl⟩,
  cases ih with k' hk',
  rw hk',
  exact ⟨k' + 1, rfl⟩,
end

/-
Theorem ev_even_iff : ∀n,
  even n ↔ ∃k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.
-/

theorem even_iff_even : even n ↔ ∃k, n = double k :=
begin
  split,
    apply even_even,
  rintro ⟨k, hk⟩,
  rw hk,
  apply even_double,
end

/-
Theorem ev_sum : ∀n m, even n → even m → even (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem even_sum (hn : even n) (hm : even m) : even (n + m) :=
begin
  induction hn with n' hn' ih,
    rw add_comm,
    exact hm,
  rw [succ_add, succ_add],
  exact ev_ss ih,
end

/-
Inductive even' : nat → Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).
-/

inductive even' : ℕ → Prop
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum {n m} (hn : even' n) (hm : even' m) : even' (n + m)

open even'

/-
Theorem even'_ev : ∀n, even' n ↔ even n.
Proof.
 (* FILL IN HERE *) Admitted.
-/

theorem even'_ev : even' n ↔ even n :=
begin
  split,
    intro h,
    induction h with n' m' hn' hm' ihn ihm,
        exact ev_0,
      exact ev_ss ev_0,
    exact even_sum ihn ihm,
  intro h,
  induction h with n' hn' ih,
    exact even'_0,
  exact even'_sum ih even'_2,
end

/-
Theorem ev_ev__ev : ∀n m,
  even (n+m) → even n → even m.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem even_add_even (hnm : even (n + m)) (hn : even n) : even m :=
begin
  induction hn with n' hn' ih,
    rwa zero_add at hnm,
  rw [succ_add, succ_add] at hnm,
  exact ih (add_two_even hnm),
end

/-
Theorem ev_plus_plus : ∀n m p,
  even (n+m) → even (n+p) → even (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
TODO: is this a good spot to introduce ac_refl?
-/

theorem even_add_add (hnm : even (n + m)) (hnp : even (n + p)) : even (m + p) :=
begin
  have h₁, exact even_sum hnm hnp,
  have : ((n + m) + (n + p)) = ((n + n) + (m + p)), ac_refl,
  rw this at h₁,
  have h₂ : even (n + n),
    rw ←double_add,
    apply even_double,
  exact even_add_even h₁ h₂,
end

/-
Inductive le : nat → nat → Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m ≤ n" := (le m n).
-/

inductive le (n : ℕ) : ℕ → Prop
| refl : le n
| step {m} (h : le m) : le (m + 1)

open le

local infix ≤ := le

/-
Theorem test_le1 :
  3 ≤ 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.

Theorem test_le2 :
  3 ≤ 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 ≤ 1) → 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2. Qed.
-/

theorem test_le₁ : 3 ≤ 3 := refl

theorem test_le₂ : 3 ≤ 6 :=
begin
  apply step,
  apply step,
  apply step,
  exact refl,
end

theorem test_le₃ (h : 2 ≤ 1) : 2 + 2 = 5 :=
by rcases h with _ | ⟨_, _, ⟨⟩⟩

/-
Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).
-/

def lt (n m) := le (n + 1) m

local infix < := lt

/-
Inductive square_of : nat → nat → Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat → nat → Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat → nat → Prop :=
  | ne_1 n : even (S n) → next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).
-/

inductive square_of : ℕ → ℕ → Prop
| sq (n : ℕ) : square_of n (n * n)

inductive next_nat : ℕ → ℕ → Prop
| nn (n : ℕ) : next_nat n (n + 1)

inductive next_even : ℕ → ℕ → Prop
| ne_1 {n} : even (n + 1) → next_even n (n + 1)
| ne_2 {n} (h : even (n + 2)) : next_even n (n + 2)

inductive total_relation : ℕ → ℕ → Prop
| intro (n₁ n₂) : total_relation n₁ n₂

inductive empty_relation : ℕ → ℕ → Prop

/-
Lemma le_trans : ∀m n o, m ≤ n → n ≤ o → m ≤ o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : ∀n,
  0 ≤ n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : ∀n m,
  n ≤ m → S n ≤ S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : ∀n m,
  S n ≤ S m → n ≤ m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_l : ∀a b,
  a ≤ a + b.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : ∀n1 n2 m,
  n1 + n2 < m →
  n1 < m ∧ n2 < m.
Proof.
 unfold lt.
 (* FILL IN HERE *) Admitted.

Theorem lt_S : ∀n m,
  n < m →
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_complete : ∀n m,
  n <=? m = true → n ≤ m.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma le_trans (hmn : m ≤ n) (hno : n ≤ o) : m ≤ o :=
begin
  induction hno with o' hno' ih,
    exact hmn,
  exact step ih,
end

theorem zero_le : 0 ≤ n :=
begin
  induction n with n' ih,
    exact refl,
  exact step ih,
end

/-
TODO: i used this earlier
-/
theorem nat.succ_le_succ (h : n ≤ m) : n + 1 ≤ m + 1 :=
begin
  induction h with m' h' ih,
    exact refl,
  exact step ih,
end

/-
TODO: i used this earlier
-/
theorem nat.le_of_succ_le_succ (h : n + 1 ≤ m + 1) : n ≤ m :=
begin
  rcases h with _ | ⟨m, h⟩,
    exact refl,
  exact le_trans (step refl) h,
end

theorem nat.le_add_right : n ≤ n + m :=
begin
  induction m with m ih,
    rw add_zero,
    exact refl,
  exact step ih,
end

theorem add_lt (h : n + m < o) : n < o ∧ m < o :=
begin
  have : ∀n m, n + 1 ≤ n + m + 1,
    intros n m,
    rw add_assoc,
    rw add_comm m,
    rw ←add_assoc,
    exact nat.le_add_right,
  split,
    exact le_trans (this n m) h,
  rw add_comm at h,
  exact le_trans (this m n) h,
end

theorem lt_lt_succ (h : n < m) : n < m + 1 := step h

theorem leb_complete (h : n ≤? m = tt) : n ≤ m :=
begin
  induction n with n ih generalizing m,
    exact zero_le,
  cases m with m,
    cases h,
  exact nat.succ_le_succ (ih h),
end

/-
Theorem leb_correct : ∀n m,
  n ≤ m →
  n <=? m = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem leb_correct (h : n ≤ m) : n ≤? m = tt :=
begin
  induction m with m ih generalizing n,
  cases h,
    refl,
  cases n,
    refl,
  exact ih (nat.le_of_succ_le_succ h),
end

/-
Theorem leb_true_trans : ∀n m o,
  n <=? m = true → m <=? o = true → n <=? o = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem leb_tt_trans (hnm : n ≤? m = tt) (hmo : m ≤? o = tt)
  : n ≤? o = tt := leb_correct (le_trans (leb_complete hnm) (leb_complete hmo))

/-
Theorem leb_iff : ∀n m,
  n <=? m = true ↔ n ≤ m.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- if you didn't do the last section -/
/- you're gonna have a bad time -/

theorem leb_iff : n ≤? m = tt ↔ n ≤ m := ⟨leb_complete, leb_correct⟩

/-
Inductive R : nat → nat → nat → Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.
-/

inductive R : ℕ → ℕ → ℕ → Prop
| c₁ : R 0 0 0
| c₂ {m n o} (h : R m n o) : R (m + 1) n (o + 1)
| c₃ {m n o} (h : R m n o) : R m (n + 1) (o + 1)
| c₄ {m n o} (h : R (m + 1) (n + 1) (o + 2)) : R m n o
| c₅ {m n o} (h : R m n o) : R n m o

open R

/-
Definition fR : nat → nat → nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem R_equiv_fR : ∀m n o, R m n o ↔ fR m n = o.
Proof.
(* FILL IN HERE *) Admitted.
-/

def fR := λ(m n : ℕ), m + n

/-
recommended - tricky induction
make fun of coq destruction naming (for once)
-/

lemma add_eq_zero : ∀{m n}, m + n = 0 → m = 0 ∧ n = 0
| 0 0 h := ⟨rfl, rfl⟩
| (m + 1) n h :=
begin
  rw succ_add at h,
  cases h,
end


theorem R_equiv_fR {m n o : ℕ} : R m n o ↔ fR m n = o :=
begin
  split,
    intro h,
    induction h,
    case c₁ : { refl },
    case c₂ : m' n' o' h ih {
      unfold fR at ih ⊢,
      rw succ_add,
      rw ih,
    },
    case c₃ : m' n' o' h ih {
      unfold fR at ih ⊢,
      have : m' + (n' + 1) = m' + n' + 1, refl,
      rw this,
      rw ih,
    },
    case c₄ : m' n' o' h ih {
      unfold fR at ih ⊢,
      have : m' + 1 + (n' + 1) = m' + n' + 1 + 1, ac_refl,
      rw this at ih,
      injections,
    },
    case c₅ : m' n' o' h ih {
      unfold fR at ih ⊢,
      rwa add_comm,
    },
  intro h,
  unfold fR at h,
  induction o with o ih generalizing m n,
    have h, exact add_eq_zero h,
    rw [h.left, h.right],
    exact c₁,
  cases m,
    cases n,
      cases h,
    injection h with h,
    exact c₃ (ih h),
  rw succ_add at h,
  injection h with h,
  exact c₂ (ih h),
end

/-
Inductive subseq : list nat → list nat → Prop :=
(* FILL IN HERE *)
.
Theorem subseq_refl : ∀(l : list nat), subseq l l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_app : ∀(l1 l2 l3 : list nat),
  subseq l1 l2 →
  subseq l1 (l2 ++ l3).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem subseq_trans : ∀(l1 l2 l3 : list nat),
  subseq l1 l2 →
  subseq l2 l3 →
  subseq l1 l3.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
starting generic since it's useful later
-/

inductive subseq : list α → list α → Prop
| em : subseq [] []
| cr {l₁ l₂} (a) (h : subseq l₁ l₂) : subseq l₁ (a :: l₂)
| cl {l₁ l₂} (a) (h : subseq l₁ l₂) : subseq (a :: l₁) (a :: l₂)

open subseq

theorem subseq_refl (l : list α) : subseq l l :=
begin
  induction l with h t ih,
    exact em,
  exact cl h ih,
end

theorem subseq_app (l₁ l₂ l₃ : list α) (h : subseq l₁ l₂)
  : subseq l₁ (l₂ ++ l₃) :=
begin
  induction h,
  case em : {
    rw nil_append,
    induction l₃ with h t ih,
      exact em,
    exact cr h ih,
  },
  case cr : l₁' l₂' n h' ih { exact cr n ih },
  case cl : l₁' l₂' n h' ih { exact cl n ih },
end

theorem subseq_trans {l₁ l₂ l₃ : list α}
  (h₁₂ : subseq l₁ l₂) (h₂₃ : subseq l₂ l₃) : subseq l₁ l₃ :=
begin
  induction h₂₃ generalizing l₁,
  case em : {
    cases h₁₂,
    exact em,
  },
  case cr : l₂' l₃' n h ih { exact cr n (ih h₁₂) },
  case cl : l₂' l₃' n h ih {
    cases h₁₂,
    case cr : l₁' l₂' n h₁₂' { exact cr n (ih h₁₂') },
    case cl : l₁' l₂' n h₁₂' { exact cl n (ih h₁₂') },
  },
end

/-
Inductive R : nat → list nat → Prop :=
  | c1 : R 0 []
  | c2 : ∀n l, R n l → R (S n) (n :: l)
  | c3 : ∀n l, R (S n) l → R n l.
-/

inductive R' : ℕ → list ℕ → Prop
| c₁' : R' 0 []
| c₂' : ∀{n l}, R' n l → R' (n + 1) (n :: l)
| c₃' : ∀{n l}, R' (n + 1) l → R' n l

open R'

example : R' 2 [1, 0] :=
begin
  apply c₂',
  apply c₂',
  exact c₁',
end

example : R' 1 [1, 2, 1, 0] :=
begin
  apply c₃',
  apply c₂',
  apply c₃',
  apply c₃',
  apply c₂',
  apply c₂',
  apply c₂',
  apply c₁',
end

/-
Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).
-/

inductive reg_exp : Type
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char (a : α) : reg_exp
| App (r₁ r₂ : reg_exp) : reg_exp
| Union (r₁ r₂ : reg_exp) : reg_exp
| Star (r : reg_exp) : reg_exp

open reg_exp

/-
Inductive exp_match {T} : list T → reg_exp → Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).
-/

inductive exp_match : list α → @reg_exp α → Prop
| MEmpty : exp_match [] EmptyStr
| MChar (a : α) : exp_match [a] (Char a)
| MApp {s₁ re₁ s₂ re₂} (h₁ : exp_match s₁ re₁) (h₂ : exp_match s₂ re₂)
  : exp_match (s₁ ++ s₂) (App re₁ re₂)
| MUnionL {s₁ re₁} re₂ (h : exp_match s₁ re₁) : exp_match s₁ (Union re₁ re₂)
| MUnionR re₁ {s₂ re₂} (h : exp_match s₂ re₂) : exp_match s₂ (Union re₁ re₂)
| MStar0 (re : reg_exp) : exp_match [] (Star re)
| MStarApp {s₁ s₂ re}
  (h₁ : exp_match s₁ re)
  (h₂ : exp_match s₂ (Star re))
  : exp_match (s₁ ++ s₂) (Star re)

open exp_match

variables {s s₁ s₂ : list α}
variables {re re₀ re₁ re₂ : @reg_exp α}

/-
Notation "s =~ re" := (exp_match s re) (at level 80).
-/

local infix ` =~ `:35 := exp_match

/-
Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.
-/

example : [1] =~ Char 1 := MChar 1

example : [1, 2] =~ App (Char 1) (Char 2) := MApp (MChar 1) (MChar 2)

/-
Example reg_exp_ex3 : ¬([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.
-/

/-
TODO: lean can't make it to the remember section
before needing generalize
-/

example : ¬([1, 2] =~ Char 1) :=
begin
  generalize heq : [1, 2] = s,
  with_cases { rintro ⟨⟩ },
  rintro ⟨⟩,
end

/-
Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] ⇒ EmptyStr
  | x :: l' ⇒ App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.
-/

def reg_exp_of_list : list α → @reg_exp α
| [] := EmptyStr
| (a :: l) := App (Char a) (reg_exp_of_list l)

example : [1, 2, 3] =~ reg_exp_of_list [1, 2, 3] :=
begin
  apply @MApp _ [1],
    apply MChar,
  apply @MApp _ [2],
    apply MChar,
  apply @MApp _ [3],
    apply MChar,
  apply MEmpty,
end

/-
Lemma MStar1 :
  ∀T s (re : @reg_exp T) ,
    s =~ re →
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.
-/

lemma MStar₁ (h : s =~ re) : s =~ Star re :=
begin
  rw ←append_nil s,
  exact MStarApp h (MStar0 re),
end

/-
Lemma empty_is_empty : ∀T (s : list T),
  ¬(s =~ EmptySet).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma MUnion' : ∀T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 ∨ s =~ re2 →
  s =~ Union re1 re2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma empty_is_empty : ¬(s =~ EmptySet) := by rintro ⟨⟩

lemma MUnion' (h : s =~ re₁ ∨ s =~ re₂) : s =~ Union re₁ re₂ :=
begin
  cases h,
    exact MUnionL re₂ h,
  exact MUnionR re₁ h,
end

/-
Lemma MStar' : ∀T (ss : list (list T)) (re : reg_exp),
  (∀s, In s ss → s =~ re) →
  fold app ss [] =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma MStar' (ss) (h : ∀{s : list α}, In s ss → s =~ re)
  : ss.foldr append [] =~ Star re :=
begin
  induction ss with s' ss ih,
    exact MStar0 re,
  apply MStarApp,
    exact h (or.inl rfl),
  apply ih,
  intros s h',
  exact h (or.inr h'),
end

/-
Lemma reg_exp_of_list_spec : ∀T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 ↔ s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma reg_exp_of_list_spec : s₁ =~ reg_exp_of_list s₂ ↔ s₁ = s₂ :=
begin
  split,
    intro h,
    induction s₂ with a₂ s₂ ih₂ generalizing s₁,
      cases h,
      refl,
    generalize heq : reg_exp_of_list (a₂::s₂) = re',
    rw heq at h,
    cases h,
    case MEmpty { cases heq, },
    case MChar : a { cases heq, },
    case MApp : s₁ re₁ s₂' re₂ h₁ h₂ {
      injection heq with h₁' h₂',
      rw ←h₁' at h₁,
      rw ←h₂' at h₂,
      cases h₁,
      unfold list.append,
      congr,
      exact ih₂ h₂,
    },
    case MUnionL : s₁ re₁ re₂ h { cases heq, },
    case MUnionR : re₁ s₂' re₂ h { cases heq, },
    case MStar0 : re { cases heq, },
    case MStarApp : s₁ s₂' re { cases heq, },
  intro h,
  induction s₂ with a₂ s₂ ih₂ generalizing s₁,
    rw h,
    exact MEmpty,
  rw h,
  unfold reg_exp_of_list,
  exact MApp (MChar a₂) (ih₂ rfl),
end

/-
Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet ⇒ []
  | EmptyStr ⇒ []
  | Char x ⇒ [x]
  | App re1 re2 ⇒ re_chars re1 ++ re_chars re2
  | Union re1 re2 ⇒ re_chars re1 ++ re_chars re2
  | Star re ⇒ re_chars re
  end.
-/

def re_chars : reg_exp → list α
| EmptySet := []
| EmptyStr := []
| (Char a) := [a]
| (App re₁ re₂) := re_chars re₁ ++ re_chars re₂
| (Union re₁ re₂) := re_chars re₁ ++ re_chars re₂
| (Star re) := re_chars re

/-
Theorem in_re_match : ∀T (s : list T) (re : reg_exp) (x : T),
  s =~ re →
  In x s →
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.
-/

theorem in_re_match (hm : s =~ re) (hi : In a s) : In a (re_chars re) :=
begin
  induction hm,
  case MEmpty { apply hi, },
  case MChar { apply hi, },
  case MApp : s₁ re₁ s₂ re₂ h₁ h₂ ih₁ ih₂ {
    unfold re_chars,
    rw in_app_iff at *,
    exact or.imp ih₁ ih₂ hi,
  },
  case MUnionL : s₁ re₁ re₂ h ih {
    unfold re_chars,
    rw in_app_iff,
    exact or.inl (ih hi),
  },
  case MUnionR : s₁ re₁ re₂ h ih {
    unfold re_chars,
    rw in_app_iff,
    exact or.inr (ih hi),
  },
  case MStar0 { cases hi, },
  case MStarApp : s₁ s₂ re h₁ h₂ ih₁ ih₂ {
    rw in_app_iff at hi,
    cases hi,
      exact ih₁ hi,
    exact ih₂ hi,
  }
end

/-
Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma re_not_empty_correct : ∀T (re : @reg_exp T),
  (∃s, s =~ re) ↔ re_not_empty re = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- yep, the lemma found errors in my first two attempts -/

def re_not_empty : @reg_exp α → bool
| EmptySet := ff
| EmptyStr := tt
| (Char _) := tt
| (App re₁ re₂) := re_not_empty re₁ && re_not_empty re₂
| (Union re₁ re₂) := re_not_empty re₁ || re_not_empty re₂
| (Star _) := tt

/-
TODO: file issues for dsimp and unfold breaking tags
-/
lemma re_not_empty_correct : (∃s, s =~ re) ↔ re_not_empty re = tt :=
begin
  split,
    /- braces so all_goals doesn't affect other direction -/
    rintro ⟨w, h⟩, {
    induction h,
      case MEmpty { rw re_not_empty, },
      case MChar : a { rw re_not_empty, },
      case MApp : s₁ re₁ s₂ re₂ h₁ h₂ ih₁ ih₂ {
        rw re_not_empty,
        rw band_eq_true_eq_eq_tt_and_eq_tt,
        exact ⟨ih₁, ih₂⟩,
      },
      case MUnionL : s₁ re₁ re₂ h ih {
        rw re_not_empty,
        rw bor_eq_true_eq_eq_tt_or_eq_tt,
        exact or.inl ih,
      },
      case MUnionR : re₁ s₂ re₂ h ih {
        rw re_not_empty,
        rw bor_eq_true_eq_eq_tt_or_eq_tt,
        exact or.inr ih,
      },
      case MStar0 : re { rw re_not_empty, },
      case MStarApp : s₁ s₂ re h₁ h₂ ih₁ ih₂ { rw re_not_empty, },
    },
  intro h,
  induction re,
  case EmptySet { cases h, },
  case EmptyStr { exact ⟨[], MEmpty⟩, },
  case Char { exact ⟨[re], MChar re⟩, },
  case App : re₁ re₂ ih₁ ih₂ {
    rw re_not_empty at h,
    rw band_eq_true_eq_eq_tt_and_eq_tt at h,
    cases (ih₁ h.left) with w₁ ih₁,
    cases (ih₂ h.right) with w₂ ih₂,
    exact ⟨w₁ ++ w₂, MApp ih₁ ih₂⟩,
  },
  case Union : re₁ re₂ ih₁ ih₂ {
    rw re_not_empty at h,
    rw bor_eq_true_eq_eq_tt_or_eq_tt at h,
    cases h,
      cases ih₁ h with w ih₁,
      exact ⟨w, MUnionL re₂ ih₁⟩,
    cases ih₂ h with w ih₂,
    exact ⟨w, MUnionR re₁ ih₂⟩,
  },
  case Star : re ih { exact ⟨[], MStar0 re⟩, },
end

/-
Lemma star_app: ∀T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re →
  s2 =~ Star re →
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl. intros H. apply H.
  - (* MChar. Stuck... *)
Abort.
-/

-- lemma star_app (h₁ : s₁ =~ Star re) (h₂ : s₂ =~ Star re)
--   : s₁ ++ s₂ =~ Star re :=
-- begin
--   induction h₁,
--   case MEmpty { exact h₂, },
--   case MChar { },
-- end

/-
Lemma star_app: ∀T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re →
  s1 =~ re' →
  s2 =~ Star re →
  s1 ++ s2 =~ Star re
Abort.
-/

-- lemma star_app {re'}
--   {heq : Star re = re'}
--   (h₁ : s₁ =~ Star re)
--   (h₂ : s₂ =~ Star re)
--   : s₁ ++ s₂ =~ Star re := sorry

/-
Lemma star_app: ∀T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re →
  s2 =~ Star re →
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.
  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.
-/

/-
ex uses discriminate with no hypothesis, so it's fair to
introduce contradiction here
-/
lemma star_app (h₁ : s₁ =~ Star re) (h₂ : s₂ =~ Star re)
  : s₁ ++ s₂ =~ Star re :=
begin
  /- generalize performs rewrites at the goal-/
  revert re,
  intro,
  generalize heq : Star re = re',
  intros,
  induction h₁ generalizing h₂,
  case MEmpty { contradiction, },
  case MChar : a { contradiction, },
  case MApp : s₁ re₁ s₂ re₂ h₁' h₂' ih₁ ih₂ { contradiction, },
  case MUnionL : s₁ re₁ re₂ h ih { contradiction},
  case MUnionR : re₁ s₂ re₂ h ih { contradiction, },
  case MStar0 : re'' { exact h₂, },
  case MStarApp : s₁ s₂ re'' h₁' h₂' ih₁ ih₂ {
    rw append_assoc,
    exact MStarApp h₁' (ih₂ heq h₂),
  },
end

/-
Lemma MStar'' : ∀T (s : list T) (re : reg_exp),
  s =~ Star re →
  ∃ss : list (list T),
    s = fold app ss []
    ∧ ∀s', In s' ss → s' =~ re.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- use permits a list, so using [] would be an empty use -/
/- use continues working on arbitrary inductive types
so can be used to eat the left side of the and in the goal
-/
lemma MStar'' (h : s =~ Star re)
  : ∃ss, s = foldr append [] ss ∧ ∀{s'}, In s' ss → s' =~ re :=
begin
  revert h,
  generalize heq : Star re = re',
  intro,
  induction h,
  case MEmpty { contradiction, },
  case MChar { contradiction, },
  case MApp { contradiction, },
  case MUnionL { contradiction, },
  case MUnionR { contradiction, },
  case MStar0 : re'' {
    use [[], rfl],
    rintro s' ⟨⟩,
  },
  case MStarApp : s₁ s₂ re' h₁ h₂ ih₁ ih₂ {
    cases ih₂ heq with w h,
    use s₁::w,
    rw h.left,
    simp,
    rintro s' (h' | h'),
      injection heq with heq',
      rw heq',
      rwa ←h',
    exact h.right h',
  },
end

/-
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet ⇒ 0
  | EmptyStr ⇒ 1
  | Char _ ⇒ 2
  | App re1 re2 ⇒
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 ⇒
      pumping_constant re1 + pumping_constant re2
  | Star _ ⇒ 1
  end
-/

def pumping_constant : @reg_exp α → ℕ
| EmptySet := 0
| EmptyStr := 1
| (Char _) := 2
| (App re₁ re₂) := pumping_constant re₁ + pumping_constant re₂
| (Union re₁ re₂) := pumping_constant re₁ + pumping_constant re₂
| (Star _) := 1

/-
Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 ⇒ []
  | S n' ⇒ l ++ napp n' l
  end.

Lemma napp_plus: ∀T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.
-/

def napp : ℕ → list α → list α
| 0 _ := []
| (n + 1) l := l ++ napp n l

lemma napp_plus : napp (n + m) s = napp n s ++ napp m s :=
begin
  induction n with n ih,
    unfold napp,
    rw [zero_add, nil_append],
  rw succ_add,
  unfold napp,
  rw append_assoc,
  rw ih,
end

/-
Import Coq.omega.Omega.
Lemma pumping : ∀T (re : @reg_exp T) s,
  s =~ re →
  pumping_constant re ≤ length s →
  ∃s1 s2 s3,
    s = s1 ++ s2 ++ s3 ∧
    s2 ≠ [] ∧
    ∀m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  (* FILL IN HERE *) Admitted.
-/

/- going back to default as finishing tactics can't handle our def -/

/- omega is less useful, but solves a couple lemmas -/

lemma le_add (h : n + m <= o) : n <= o ∧ m <= o := by omega

lemma add_le_add' (h: n + m <= o + p) : n <= o ∨ m <= p := by omega

lemma one_le (h : 1 <= n + m) : 1 <= n ∨ 1 <= m := by omega

lemma napp_star (h₁ : s₁ =~ re) (h₂ : s₂ =~ Star re)
  : napp n s₁ ++ s₂ =~ Star re :=
begin
  induction n with n ih,
    unfold napp,
    rwa nil_append,
  unfold napp,
  rw append_assoc,
  exact MStarApp h₁ ih,
end

lemma pumping (hm : s =~ re) (hp : pumping_constant re <= s.length)
  : ∃{s₁ s₂ s₃},
  s = s₁ ++ s₂ ++ s₃ ∧ s₂ ≠ [] ∧ ∀{m}, s₁ ++ napp m s₂ ++ s₃ =~ re :=
begin
  induction hm,
  case MEmpty { cases hp, },
  case MChar : a { rcases hp with _ | ⟨_, _, ⟨⟩⟩, },
  case MApp : s₁ re₁ s₂ re₂ h₁ h₂ ih₁ ih₂ {
    unfold pumping_constant at hp,
    rw length_append at hp,
    cases add_le_add' hp,
      rcases ih₁ h with ⟨s₁', s₂', s₃, rfl, h₂', h₃⟩,
      use [s₁', s₂', s₃ ++ s₂],
      rw append_assoc,
      use [rfl, h₂'],
      intro m,
      rw ←append_assoc,
      exact MApp h₃ h₂,
    rcases ih₂ h with ⟨s₁', s₂', s₃, rfl, h₂', h₃⟩,
    use [s₁ ++ s₁', s₂', s₃],
    rw [←append_assoc, ←append_assoc],
    use [rfl, h₂'],
    intro m,
    rw [append_assoc, append_assoc],
    apply MApp h₁,
    rw ←append_assoc,
    exact h₃,
  },
  case MUnionL : s₁ re₁ re₂ h ih {
    unfold pumping_constant at hp,
    rcases ih (le_add hp).left with ⟨s₁', s₂, s₃, rfl, h₂, h₃⟩,
    use [s₁', s₂, s₃, rfl, h₂],
    intro m,
    apply MUnionL,
    exact h₃,
  },
  case MUnionR : re₁ s₂ re₂ h ih {
    unfold pumping_constant at hp,
    rcases ih (le_add hp).right with ⟨s₁, s₂', s₃, rfl, h₂, h₃⟩,
    use [s₁, s₂', s₃, rfl, h₂],
    intro m,
    apply MUnionR,
    exact h₃,
  },
  case MStar0 : re { cases hp, },
  case MStarApp : s₁ s₂ re h₁ h₂ ih₁ ih₂ {
    rw length_append at hp,
    cases one_le hp,
      use [[], s₁, s₂, rfl, ne_nil_of_length_pos h],
      intro m,
      rw nil_append,
      exact napp_star h₁ h₂,
    rcases ih₂ h with ⟨s₁', s₂', s₃, rfl, h₂, h₃⟩,
    use [s₁ ++ s₁', s₂', s₃],
    rw [←append_assoc, ←append_assoc],
    use [rfl, h₂],
    intro m,
    rw [append_assoc, append_assoc],
    apply MStarApp h₁,
    rw ←append_assoc,
    exact h₃,
  },
end

/-
Theorem filter_not_empty_In : ∀n l,
  filter (fun x ⇒ n =? x) l ≠ [] →
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.
-/

theorem filter_not_empty_In {l} (h : filter (λx, n =? x) l ≠ []) : In n l :=
begin
  induction l with m l ih,
    apply h,
    refl,
  cases heq : n =? m,
    right,
    apply ih,
    unfold filter at h,
    rwa heq at h,
  left,
  rw eqb_eq at heq,
  rw heq,
end

/-
Inductive reflect (P : Prop) : bool → Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ¬P) : reflect P false.
-/

/-
TODO: replace with decidable
-/

inductive reflect (P : Prop) : bool → Prop
| ReflectT (h : P) : reflect tt
| ReflectF (h : ¬P) : reflect ff

open reflect

/-
Theorem iff_reflect : ∀P b, (P ↔ b = true) → reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.
-/

theorem iff_reflect {b} (h : P ↔ b = tt) : reflect P b :=
begin
  cases b,
    apply ReflectF,
    rw h,
    simp,
  apply ReflectT,
  rw h,
end

/-
Theorem reflect_iff : ∀P b, reflect P b → (P ↔ b = true).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem reflect_iff {b} (h : reflect P b) : (P ↔ b = tt) :=
begin
  cases h with h' h',
    rw eq_self_iff_true,
    rwa iff_true,
  simp only [iff_false],
  exact h',
end

/-
Lemma eqbP : ∀n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.
-/

lemma eqbP : reflect (n = m) (n =? m) :=
begin
  apply iff_reflect,
  rw eqb_eq,
end

/-
Theorem filter_not_empty_In' : ∀n l,
  filter (fun x ⇒ n =? x) l ≠ [] →
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.
-/

theorem filter_not_empty_In' {l} (h : filter (λ x, n =? x) l ≠ []) : In n l :=
begin
  induction l with m l ih,
    apply h,
    refl,
  have, exact @eqbP n m,
  generalize heq : n =? m = eq,
  generalize heq' : n = m = eq',
  rw [heq, heq'] at this,
  cases this,
  case ReflectT : this' {
    rw ←heq' at this',
    rw this',
    exact or.inl rfl,
  },
  case ReflectF : this' {
    unfold filter at h,
    rw heq at h,
    exact or.inr (ih h),
  },
end

/-
Fixpoint count n l :=
  match l with
  | [] ⇒ 0
  | m :: l' ⇒ (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : ∀n l,
  count n l = 0 → ~(In n l).
Proof.
  (* FILL IN HERE *) Admitted.
-/

def count (n) : list ℕ → ℕ
| [] := 0
| (m :: l) := (if n =? m then 1 else 0) + count l

/-
TODO: introduced revert_after for hypothesis management to make
generalize work nicer
-/

theorem eqbP_practice' {l} (h : count n l = 0) : ¬In n l :=
begin
  induction l with m l ih,
    rintro ⟨⟨⟩⟩,
  unfold count at h,
  have, exact @eqbP n m,
  revert_after ih,
  generalize heq : n = m = eq,
  generalize heq' : n =? m = eq',
  intros h h',
  cases h',
  case ReflectT : h' {
    simp only [if_true, bool.coe_sort_tt] at h,
    rw add_comm at h,
    contradiction,
  },
  case ReflectF : h' {
    simp only [bool.coe_sort_ff, if_false] at h,
    rintro (c | c),
      rw c at heq,
      simp only [true_iff, eq_self_iff_true, eq_iff_iff] at heq,
      contradiction,
    rw zero_add at h,
    exact absurd c (ih h),
  },
end

/-
Inductive nostutter {X:Type} : list X → Prop :=
 (* FILL IN HERE *)
.
-/

inductive nostutter : list α → Prop
| no₀ : nostutter []
| no₁ (a) : nostutter [a]
| no₂ (a) {h t} (n : nostutter (h :: t)) (hne : a ≠ h)
  : nostutter (a :: h::t)

open nostutter

/-
Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_2: nostutter (@nil nat).
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_3: nostutter [5].
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply eqb_false; auto. Qed.
*)

Example test_nostutter_4: not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(*
  Proof. intro.
  repeat match goal with
    h: nostutter _ ⊢ _ => inversion h; clear h; subst
  end.
  contradiction Hneq0; auto. Qed.
*)
-/

example : nostutter [3, 1, 4, 1, 5, 6] :=
by repeat { constructor, }; omega

example : @nostutter ℕ [] :=
by repeat { constructor, }; omega

example : nostutter [5] :=
by repeat { constructor, }; omega

/- not converting ltac for this -/
example : ¬nostutter [3, 1, 1, 4] :=
begin
  by_contra c,
  repeat { contradiction <|> cases c with _ _ _ _ c h },
end

inductive merge : list α → list α → list α → Prop
| m₀ : merge [] [] []
| ml (h) {t r m} (hm : merge t r m) : merge (h :: t) r (h :: m)
| mr {l} (h) {t m} (hm : merge l t m) : merge l (h :: t) (h :: m)

open merge

example : merge [1, 2, 3] [4, 5, 6] [1, 2, 3, 4, 5, 6] :=
by repeat { constructor, }

example : merge [1, 2, 3] [4, 5, 6] [4, 5, 6, 1, 2, 3] :=
by repeat { constructor, }

example : merge [1, 2, 3] [4, 5, 6] [1, 4, 2, 5, 3, 6] :=
by repeat { constructor, }

/-
need λ for coe from bool to Prop
TODO : maybe change p to return a decidable prop
-/

lemma filter_merge {l r m} {p : α → bool}
  (hm : merge l r m)
  (hf : ∀a, In a l → p a = ff)
  (ht : ∀a, In a r → p a = tt)
  : m.filter (λa, p a) = r :=
begin
  induction hm,
  case m₀ { refl, },
  case ml : h t r m hm ih {
    have : p h = ff,
      apply hf,
      use rfl,
    unfold filter,
    rw this,
    simp only [bool.coe_sort_ff, if_false],
    apply ih,
      intros a hin,
      unfold In at hf,
      exact hf a (or.inr hin),
    intros a hin,
    exact ht a hin,
  },
  case mr : l h t m hm ih {
    have : p h = tt,
      apply ht,
      use rfl,
    unfold filter,
    rw this,
    simp only [if_true, bool.coe_sort_tt],
    use rfl,
    apply ih,
      intros a hin,
      exact hf a hin,
    intros a hin,
    unfold In at ht,
    exact ht a (or.inr hin),
  },
end

/- filter challenge 2 -/

theorem filter_longest_matching_subseq
  {l₁ l₂ : list α} {p : α → bool}
  (hs : subseq l₁ l₂)
  (ht : l₁.all p)
  : l₁.length ≤ (l₂.filter (λa, p a)).length :=
begin
  induction hs,
  case em { exact refl, },
  case cr : l₁' l₂' a h ih {
    apply le_trans (ih ht),
    unfold filter,
    cases p a,
      exact refl,
    exact step refl,
  },
  case cl : l₁' l₂' a h ih {
    unfold filter,
    unfold list.all foldr at ht,
    simp only [band_coe_iff] at ht,
    simp only [ht.left, if_true],
    unfold list.length,
    apply nat.succ_le_succ,
    exact ih ht.right,
  },
end

section palindrome

open poly (
  append_assoc nil_append reverse_append
  reverse_involutive
)
open poly.list

local infix :: := cons
local infix ++ := append
local notation `[]` := nil
local notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

variable {l : poly.list α}

inductive pal : poly.list α → Prop
| pal₀ : pal []
| pal₁ (a) : pal [a]
| pal₂ (a) {l} (h : pal l) : pal (a :: l ++ [a])

open pal

example : pal [1, 2, 1] := pal₂ 1 (pal₁ 2)

lemma pal_app_rev : pal (l ++ l.reverse) :=
begin
  induction l with a l ih,
    exact pal₀,
  rw poly.cons_append,
  rw reverse,
  rw poly.append_assoc,
  exact pal₂ a ih,
end

lemma pal_rev (p : pal l) : l = l.reverse :=
begin
  induction p,
  case pal₀ { refl, },
  case pal₁ { refl, },
  case pal₂ : h t hp ih {
    rw poly.cons_append,
    unfold reverse,
    rw reverse_append,
    unfold reverse,
    unfold poly.list.append,
    rw ←ih,
  },
end

/-
palindrome converse
-/

theorem nat.le_of_succ_le (h : n + 1 ≤ m) : n ≤ m := le_trans (step refl) h

theorem nat.le_add_left : n ≤ m + n :=
begin
  induction m with m ih,
    rw zero_add,
    exact refl,
  rw succ_add,
  exact step ih,
end

lemma one_le_cons_length (a : α) (l : poly.list α) : 1 ≤ (a :: l).length :=
by apply nat.le_add_left

lemma has_snoc {l : poly.list α} (h : 1 ≤ l.length) : ∃ll ar, l = ll ++ [ar] :=
begin
  induction l with a l ih,
    cases h,
  cases l with a' l,
    use [[], a],
    rw poly.nil_append,
  rcases ih (one_le_cons_length a' l) with ⟨ll, ar, ih⟩,
  use [a :: ll, ar],
  rw ih,
  rw poly.cons_append,
end

lemma length_append_cons (a l') (h : l = l' ++ [a])
  : l.length = l'.length + 1 :=
begin
  induction l' with a' l' ih generalizing l,
    cases l with a'' l,
      cases h,
    cases h,
    refl,
  cases l with a'' l,
    cases h,
  cases h,
  unfold length,
  simp only [add_left_inj],
  exact ih rfl,
end

lemma append_cons_eq_length {l₁ l₂ : poly.list α} {a₁ a₂}
  (h : l₁ ++ [a₁] = l₂ ++ [a₂]) : l₁.length = l₂.length :=
begin
  replace h, exact congr_arg length h,
  rw length_append_cons a₁ l₁ rfl at h,
  rw length_append_cons a₂ l₂ rfl at h,
  rwa add_left_inj at h,
end

lemma append_cons_eq {l₁ l₂ : poly.list α} {a₁ a₂}
  (h : l₁ ++ [a₁] = l₂ ++ [a₂]) : l₁ = l₂ ∧ a₁ = a₂ :=
begin
  have hl, exact append_cons_eq_length h,
  induction l₁ with a₁' l₁ ih generalizing l₂,
    cases l₂ with a₂' l₂,
      cases h,
      use [rfl, rfl],
    cases hl,
  cases l₂ with a₂' l₂,
    cases hl,
  injections with h₁ h₂ h₃,
  rw h₁,
  simp only [true_and, eq_self_iff_true],
  exact ih h₂ h₃,
end

lemma rev_cons_snoc {al ar : α} {lm : poly.list α}
  (h : al :: lm ++ [ar] = (al :: lm ++ [ar]).reverse)
  : al = ar ∧ lm = lm.reverse :=
begin
  rw poly.cons_append at h,
  unfold reverse at h,
  rw reverse_append at h,
  injections with h₁ h₂,
  rw poly.nil_append at h₂,
  use [h₁, (append_cons_eq h₂).left],
end

lemma rev_pal_aux (hr : l = l.reverse) (n) (hl : l.length ≤ n) : pal l :=
begin
  induction n with n ih generalizing l,
    cases l with a l,
      exact pal₀,
    cases hl,
  cases l with a l,
    exact pal₀,
  cases l with a' l,
    exact pal₁ a,
  rcases has_snoc (one_le_cons_length a' l) with ⟨ll, ar', h⟩,
  rw h at hl hr ⊢,
  rcases rev_cons_snoc hr with ⟨rfl, hr'⟩,
  have hl' : ll.length ≤ n,
    unfold length at hl,
    rw length_append_cons a ll rfl at hl,
    exact nat.le_of_succ_le (nat.le_of_succ_le_succ hl),
  exact pal₂ a (ih hr' hl'),
end

lemma rev_pal (h : l = l.reverse) : pal l :=
by exact rev_pal_aux h l.length refl

end palindrome

/- very different from builtin -/

inductive disjoint : list α → list α → Prop
| dis₀ : disjoint [] []
| disl (h) {t r} (d : disjoint t r) (hn : ¬In h r) : disjoint (h :: t) r
| disr (h) {l t} (d : disjoint l t) (hn : ¬In h l) : disjoint l (h :: t)

open indprop.disjoint

inductive nodup : list α → Prop
| nodup₀ : nodup []
| nodup₁ (h) {l} (n : nodup l) (hn : ¬In h l) : nodup (h :: l)

open nodup

example : nodup [1, 2, 3, 4] :=
begin
  repeat {constructor},
  repeat {unfold In <|> simp only [not_false_iff, or_false] <|> omega },
end

example : @nodup bool [] := nodup₀

example : ¬nodup [1, 2, 1] :=
begin
  by_contra c,
  cases c with _ _ h hn,
  unfold In at hn,
  simp only [eq_self_iff_true, not_true, or_false, or_true] at hn,
  exact hn,
end

example : ¬nodup [tt, tt] :=
begin
  by_contra c,
  cases c with _ _ n hn,
  unfold In at hn,
  simp only [eq_self_iff_true, not_true, or_false] at hn,
  exact hn,
end

lemma nil_dis (l : list α) : disjoint l [] :=
begin
  induction l with h t ih,
    exact dis₀,
  apply disl h ih,
  exact not_false,
end

lemma dis_nil (r : list α) : disjoint [] r :=
begin
  induction r with h t ih,
    exact dis₀,
  apply disr h ih,
  exact not_false,
end

lemma dis_iso {l r : list α}
  : disjoint l r ↔ (∀a, In a l → ¬In a r) ∧ (∀a, In a r → ¬In a l) :=
begin
  split,
    intro h,
    induction h,
    case dis₀ {
      rw and_self,
      rintro a ⟨⟩,
    },
    case disl : h' t r' d hn ih {
      split,
        cases ih with ihl ihr,
        rintro a (rfl | h'') c,
          exact absurd c hn,
        exact absurd h'' (ihr a c),
      cases ih with ihl ihr,
      rintros a h'' (rfl | c),
        exact absurd h'' hn,
      exact absurd h'' (ihl a c),
    },
    case disr : h' l' t d hn ih {
      split,
        cases ih with ihl ihr,
        rintros a h'' (rfl | c),
          exact absurd h'' hn,
        exact absurd h'' (ihr a c),
      cases ih with ihl ihr,
      rintros a (rfl | h'') c,
        exact absurd c hn,
      exact absurd h'' (ihl a c),
    },
  rintro ⟨hl, hr⟩,
  induction l with a l ih generalizing r,
    exact dis_nil r,
  have : disjoint l r,
    apply ih,
      intros a h',
      exact hl a (or.inr h'),
    intros a h',
    have, exact hr a h',
    rw In at this,
    exact (not_or_distrib.mp this).right,
  refine disl a this _,
  apply hl,
  exact or.inl rfl,
end

lemma dis_cons {l r} (d : disjoint (a :: l) r) : ¬In a r ∧ disjoint l r :=
begin
  rcases dis_iso.mp d with ⟨dl, dr⟩,
  split,
    by_contra c,
    have, exact dr a c,
    rw [In, not_or_distrib] at this,
    exact this.left rfl,
  rw dis_iso,
  split,
    intros a h',
    apply dl,
    exact or.inr h',
  intros a h',
  have, exact dr a h',
  rw [In, not_or_distrib] at this,
  exact this.right,
end

lemma nodup_cons {l} (hn : nodup (a :: l)) : nodup l :=
begin
  cases hn with _ _ n hn,
  exact n,
end

lemma nodup_app {l r : list α} (hn : nodup (l ++ r)) : nodup l ∧ nodup r :=
begin
  induction l,
  case nil {
    simp at hn,
    exact ⟨nodup₀, hn⟩,
  },
  case cons : hd tl ih {
    cases hn with _ _ n hn,
    have, exact ih n,
    refine ⟨nodup₁ hd this.left _, this.right⟩,
    change ¬In hd (tl ++ r) at hn,
    rw in_app_iff at hn,
    rw not_or_distrib at hn,
    exact hn.left,
  }
end

lemma app_disjoint {l r : list α}
  (hl : nodup l) (hr : nodup r) (hd : disjoint l r) : nodup (l ++ r) :=
begin
  rw dis_iso at hd,
  cases hd with hdl hdr,
  induction hl generalizing r,
  case nodup₀ {
    simp,
    exact hr,
  },
  case nodup₁ : h t n hn ih {
    rw cons_append,
    have : nodup (t ++ r),
      apply ih hr,
        intros a h',
        exact hdl a (or.inr h'),
      intros a h' c,
      have, exact hdr a h',
      rw [In, not_or_distrib] at this,
      exact absurd c this.right,
    refine nodup₁ h this _,
    by_contra c,
    rcases in_app_iff.mp c with c | c,
      exact absurd c hn,
    have : ¬In h r,
      apply hdl h,
      exact or.inl rfl,
    exact absurd c this,
  },
end

/-
Lemma in_split : ∀(X:Type) (x:X) (l:list X),
  In x l →
  ∃l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma in_split {l} (hin : In a l) : ∃l₁ l₂, l = l₁ ++ a :: l₂ :=
begin
  induction l with a' l ih,
    cases hin,
  rcases hin with rfl | hin,
    use [[], l],
    rw nil_append,
  have, exact ih hin,
  rcases (ih hin) with ⟨w₁, w₂, rfl⟩,
  use [a'::w₁, w₂],
  rw cons_append,
end

/-
Inductive repeats {X:Type} : list X → Prop :=
  (* FILL IN HERE *)
.
-/

inductive repeats : list α → Prop
| r₀ {a} {l} (hin : In a l) : repeats (a :: l)
| r₁ (a) {l} (r : repeats l) : repeats (a :: l)

open repeats

/-
Theorem pigeonhole_principle: ∀(X:Type) (l1 l2:list X),
   excluded_middle →
   (∀x, In x l1 → In x l2) →
   length l2 < length l1 →
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* FILL IN HERE *) Admitted.
-/

section pigeon

/-
TODO - don't use classical
-/
open classical

theorem pigeonhole_principle {l₁ l₂ : list α}
  (h : ∀a, In a l₁ → In a l₂) (hl : l₂.length < l₁.length) : repeats l₁ :=
begin
  induction l₁ with a₁ l₁ ih generalizing l₂,
    cases hl,
  cases l₂ with a₂ l₂,
    cases h a₁ (or.inl rfl),
  cases (em (In a₁ l₁)) with hi₁ hni₁,
    exact r₀ hi₁,
  apply r₁,
  rcases @in_split α a₁ (a₂::l₂) (h a₁ (or.inl rfl)) with ⟨l₂', l₃, heq⟩,
  apply @ih (l₂' ++ l₃),
    intros a hi₁,
    rcases h a (or.inr hi₁) with rfl | hi₂,
      cases l₂' with a₂' l₂',
        cases heq,
        exact absurd hi₁ hni₁,
      cases heq,
      exact or.inl rfl,
    cases l₂' with a₂' l₂',
      cases heq,
      exact hi₂,
    cases heq,
    rw in_app_iff,
    rcases in_app_iff.mp hi₂ with hi₂' | rfl | hi₃,
        exact or.inl (or.inr hi₂'),
      exact absurd hi₁ hni₁,
    exact or.inr hi₃,
  replace heq, exact congr_arg list.length heq,
  rw length_append at heq ⊢,
  unfold list.length at hl heq ⊢,
  rw heq at hl,
  rw ←add_assoc at hl,
  unfold lt at hl ⊢,
  exact nat.le_of_succ_le_succ hl,
end

end pigeon

/-
Require Export Coq.Strings.Ascii.
Definition string := list ascii.
-/

/-
TODO: explain this
-/
def str := list char
instance : has_append str := ⟨list.append⟩

/-
Lemma provable_equiv_true : ∀(P : Prop), P → (P ↔ True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.
-/

lemma iff_true_intro (p : P) : P ↔ true :=
begin
  split,
    intro,
    constructor,
  intro,
  exact p,
end

/-
Lemma not_equiv_false : ∀(P : Prop), ¬P → (P ↔ False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.
-/

lemma iff_false_intro (np : ¬P) : (P ↔ false) :=
begin
  split,
    apply np,
  intro h,
  cases h,
end

/-
Lemma null_matches_none : ∀(s : string), (s =~ EmptySet) ↔ False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.
-/

lemma null_matches_none : s =~ EmptySet ↔ false :=
begin
  apply iff_false_intro,
  by_contra c,
  cases c,
end

/-
Lemma empty_matches_eps : ∀(s : string), s =~ EmptyStr ↔ s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.
-/

lemma empty_matches_eps : s =~ EmptyStr ↔ s = [] :=
begin
  split,
    intro h,
    cases h,
    refl,
  intro h,
  rw h,
  exact MEmpty,
end

/-
Lemma empty_nomatch_ne : ∀(a : ascii) s, (a :: s =~ EmptyStr) ↔ False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.
-/

lemma empty_nomatch_ne : a :: s =~ EmptyStr ↔ false :=
begin
  apply iff_false_intro,
  generalize heq : a :: s = re,
  by_contra c,
  cases c,
  cases heq,
end

/-
Lemma char_nomatch_char :
  ∀(a b : ascii) s, b ≠ a → (b :: s =~ Char a ↔ False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.
-/

lemma char_nomatch_char {b} (hne : b ≠ a) : b :: s =~ Char a ↔ false :=
begin
  apply iff_false_intro,
  generalize heq : b :: s = re,
  by_contra c,
  apply hne,
  cases c,
  cases heq,
  refl,
end

/-
Lemma char_eps_suffix : ∀(a : ascii) s, a :: s =~ Char a ↔ s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.
-/

lemma char_eps_suffix : a :: s =~ Char a ↔ s = [] :=
begin
  split,
    generalize heq : a :: s = re,
    intro h,
    cases h,
    cases heq,
    refl,
  intro h,
  rw h,
  apply MChar,
end

/-
Lemma app_exists : ∀(s : string) re0 re1,
    s =~ App re0 re1 ↔
    ∃s0 s1, s = s0 ++ s1 ∧ s0 =~ re0 ∧ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. ∃s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.
-/

lemma app_exists
  : s =~ App re₀ re₁ ↔
    ∃s₀ s₁, s = s₀ ++ s₁ ∧ s₀ =~ re₀ ∧ s₁ =~ re₁ :=
begin
  split,
    rintro (_ | _ | ⟨s₁, re₁, s₂, re₂, h₁, h₂⟩),
    exact ⟨s₁, s₂, rfl, h₁, h₂⟩,
  rintro ⟨w₁, w₂, rfl, hl, hr⟩,
  exact MApp hl hr,
end

/-
Lemma app_ne : ∀(a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) ↔
    ([ ] =~ re0 ∧ a :: s =~ re1) ∨
    ∃s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re0 ∧ s1 =~ re1.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma app_ne
  : a :: s =~ App re₀ re₁ ↔
    [] =~ re₀ ∧ a :: s =~ re₁ ∨
    ∃s₀ s₁, s = s₀ ++ s₁ ∧ a :: s₀ =~ re₀ ∧ s₁ =~ re₁ :=
begin
  split,
    intro h,
    rw app_exists at h,
    rcases h with ⟨_ | ⟨h₀, t₀⟩, w₁, hl, hr⟩,
      rw nil_append at hl,
      rw ←hl at hr,
      exact or.inl hr,
    injection hl with hll hlr,
    cases hr with hrl hrr,
    rw ←hll at hrl,
    exact or.inr ⟨t₀, w₁, hlr, hrl, hrr⟩,
  rw app_exists,
  rintro (⟨hl, hr⟩ | ⟨w₀, w₁, rfl, hl, hr⟩),
    exact ⟨[], a :: s, rfl, hl, hr⟩,
  use [a :: w₀, w₁, rfl, hl, hr],
end

/-
Lemma union_disj : ∀(s : string) re0 re1,
    s =~ Union re0 re1 ↔ s =~ re0 ∨ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.
-/

lemma union_disj : s =~ Union re₀ re₁ ↔ s =~ re₀ ∨ s =~ re₁ :=
begin
  split,
    intro h,
    cases h,
    case MUnionL : _ _ _ h { exact or.inl h, },
    case MUnionR : _ _ _ h { exact or.inr h, },
  intro h,
  cases h,
    exact MUnionL re₁ h,
  exact MUnionR re₀ h,
end

/-
Lemma star_ne : ∀(a : ascii) s re,
    a :: s =~ Star re ↔
    ∃s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re ∧ s1 =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
TODO: examine whether it's reasonable to use
all_goals { try { contradiction } } here
-/

lemma star_ne
  : a :: s =~ Star re ↔
    ∃s₀ s₁, s = s₀ ++ s₁ ∧ a :: s₀ =~ re ∧ s₁ =~ Star re :=
begin
  split,
    generalize heq : a :: s = s',
    generalize heq' : Star re = re',
    intro h,
    induction h,
    case MStarApp : s₁ s₂ re'' h₁ h₂ ih₁ ih₂ {
      rw ←heq' at *,
      cases s₁,
      case nil {
        simp at heq,
        exact ih₂ heq (refl _),
      },
      case cons : hd tl {
        injection heq' with heq'',
        rw ←heq'' at *,
        injection heq with heq₁ heq₂,
        rw ← heq₁ at *,
        exact ⟨tl, s₂, heq₂, h₁, h₂⟩,
      },
    },
    case MEmpty { cases heq, },
    case MChar { cases heq', },
    case MApp { cases heq', },
    case MUnionL { cases heq', },
    case MUnionR { cases heq', },
    case MStar0 { cases heq, },
  rintro ⟨w₀, w₁, rfl, hl, hr⟩,
  rw ←cons_append,
  exact MStarApp hl hr,
end

/-
Definition refl_matches_eps m :=
  ∀re : @reg_exp ascii, reflect ([ ] =~ re) (m re).
-/

def refl_matches_eps (m : @reg_exp α → bool) := ∀re, reflect ([] =~ re) (m re)

/-
Fixpoint match_eps (re: @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def match_eps : @reg_exp α → bool
| EmptyStr := tt
| (Union re₁ re₂) := match_eps re₁ || match_eps re₂
| (Star _) := tt
| (App re₁ re₂) := match_eps re₁ && match_eps re₂
| _ := ff

/-
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* FILL IN HERE *) Admitted.
-/


lemma append_eq_nil {ll lr : list α} (h : [] = ll ++ lr): ll = [] ∧ lr = [] :=
begin
  cases ll with a ll,
    rw nil_append at h,
    rw h,
    use [rfl, rfl],
  cases h,
end

/- yeah, lean does not do well here -/
lemma match_eps_refl : @refl_matches_eps α match_eps :=
begin
  unfold refl_matches_eps,
  intro re,
  induction re,
  case EmptySet {
    unfold match_eps,
    apply ReflectF,
    rw null_matches_none,
    exact not_false,
  },
  case EmptyStr {
    unfold match_eps,
    apply ReflectT,
    exact MEmpty,
  },
  case Char : a {
    unfold match_eps,
    apply ReflectF,
    generalize heq : [] = s,
    by_contra c,
    cases c,
    cases heq,
  },
  case App : re₁ re₂ ih₁ ih₂ {
    revert_after re₂,
    generalize heq₁ : ([] =~ re₁) = re₁',
    generalize hmeq₁ : match_eps re₁ = m₁',
    generalize heq₂ : ([] =~ re₂) = re₂',
    generalize hmeq₂ : match_eps re₂ = m₂',
    unfold match_eps,
    intros,
    cases ih₁,
    case ReflectT : ih₁' {
      rw ←heq₁ at ih₁',
      cases ih₂,
      case ReflectT : ih₂' {
        rw [hmeq₁, hmeq₂],
        apply ReflectT,
        rw ←heq₂ at ih₂',
        exact MApp ih₁' ih₂',
      },
      case ReflectF : ih₂' {
        rw [hmeq₁, hmeq₂],
        apply ReflectF,
        rw ←heq₂ at ih₂',
        generalize heq : [] = s,
        rintro (_ | _ | ⟨s₁, re₁, s₂, re₂, h₁, h₂⟩),
        rcases append_eq_nil heq with ⟨rfl, rfl⟩,
        exact absurd h₂ ih₂',
      },
    },
    case ReflectF : ih₁' {
      rw ←heq₁ at ih₁',
      rw [hmeq₁, hmeq₂],
      apply ReflectF,
      generalize heq : [] = s,
      rintro (_ | _ | ⟨s₁, re₁, s₂, re₂, h₁, h₂⟩),
      rcases append_eq_nil heq with ⟨rfl, rfl⟩,
      exact absurd h₁ ih₁',
    },
  },
  case Union : re₁ re₂ ih₁ ih₂ {
    revert_after re₂,
    generalize heq₁ : ([] =~ re₁) = re₁',
    generalize hmeq₁ : match_eps re₁ = m₁',
    generalize heq₂ : ([] =~ re₂) = re₂',
    generalize hmeq₂ : match_eps re₂ = m₂',
    unfold match_eps,
    intros,
    cases ih₁,
    case ReflectT : ih₁' {
      rw [hmeq₁, hmeq₂],
      rw ←heq₁ at ih₁',
      exact ReflectT (MUnionL re₂ ih₁'),
    },
    case ReflectF : ih₁' {
      rw ←heq₁ at ih₁',
      cases ih₂,
      case ReflectT : ih₂' {
        rw [hmeq₁, hmeq₂],
        rw ←heq₂ at ih₂',
        exact ReflectT (MUnionR re₁ ih₂'),
      },
      case ReflectF : ih₂' {
        rw [hmeq₁, hmeq₂],
        rw ←heq₂ at ih₂',
        apply ReflectF,
        rw union_disj,
        rintro (c | c),
          exact absurd c ih₁',
        exact absurd c ih₂',
      },
    },
  },
  case Star : r ih {
    unfold match_eps,
    exact ReflectT (MStar0 r),
  },
end

/-
Definition is_der re (a : ascii) re' :=
  ∀s, a :: s =~ re ↔ s =~ re'.
-/

def is_der (a : α) (re₀ re₁) := ∀s, a :: s =~ re₀ ↔ s =~ re₁

/-
Definition derives d := ∀a re, is_der re a (d a re).
-/

def derives (d : α → @reg_exp α → @reg_exp α) := ∀a re, is_der a re (d a re)

/-
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

/-
TODO: look into deciable eq
-/
def derive (a : char) : @reg_exp char → @reg_exp char
| EmptySet := EmptySet
| EmptyStr := EmptySet
| (Char a') := if a = a' then EmptyStr else EmptySet
| (App re₁ re₂) := if match_eps re₁
                   then Union (App (derive re₁) re₂) (derive re₂)
                   else App (derive re₁) re₂
| (Union re₁ re₂) := Union (derive re₁) (derive re₂)
| (Star re) := App (derive re) (Star re)

/-
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.
-/

def c := 'c'
def d := 'd'

/-
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive c (EmptySet)) = ff := rfl

/-
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive c (Char c)) = tt := rfl

/-
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive c (Char d)) = ff := rfl

/-
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive c (App (Char c) EmptyStr)) = tt := rfl

/-
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive c (App EmptyStr (Char c))) = tt := rfl

/-
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive c (Star (Char c))) = tt := rfl

/-
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive d (derive c (App (Char c) (Char d)))) = tt := rfl

/-
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* FILL IN HERE *) Admitted.
-/

example : match_eps (derive d (derive c (App (Char d) (Char c)))) = ff := rfl

/-
Lemma derive_corr : derives derive.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
TODO: is this a good spot to introduce refine?
-/
lemma derive_corr : derives derive :=
begin
  unfold derives,
  unfold is_der,
  intros,
  split,
    generalize heq : a :: s = s',
    intro h,
    induction re generalizing s s',
    case EmptySet { cases h, },
    case EmptyStr {
      cases h,
      cases heq,
    },
    case Char {
      cases h,
      cases heq,
      unfold derive,
      simp only [if_true, eq_self_iff_true],
      exact MEmpty,
    },
    case App : re₁ re₂ ih₁ ih₂ {
      unfold derive,
      rw [←heq, app_ne] at h,
      have, exact match_eps_refl re₁,
      revert this,
      generalize heq' : ([] =~ re₁) = re₁',
      generalize heq'' : match_eps re₁ = me',
      intro,
      rcases h with ⟨h₁, h₂⟩ | ⟨s₀, s₁, rfl, h₁, h₂⟩,
        cases this,
        case ReflectT : this {
          simp only [if_true, bool.coe_sort_tt],
          apply MUnionR,
          exact ih₂ s (a :: s) rfl h₂,
        },
        case ReflectF : this {
          rw ←heq' at this,
          cases this with hl hr,
          exact absurd h₁ hr,
        },
      cases this,
      case ReflectT : this {
        apply MUnionL,
        rw app_exists,
        refine ⟨s₀, s₁, rfl, _, h₂⟩,
        exact ih₁ s₀ (a :: s₀) rfl h₁,
      },
      case ReflectF : this {
        simp only [bool.coe_sort_ff, if_false],
        rw app_exists,
        refine ⟨s₀, s₁, rfl, _, h₂⟩,
        exact ih₁ s₀ (a :: s₀) rfl h₁,
      },
    },
    case Union : re₁ re₂ ih₁ ih₂ {
      unfold derive,
      rcases union_disj.mp h with h | h,
        apply MUnionL,
        exact ih₁ s s' heq h,
      apply MUnionR,
      exact ih₂ s s' heq h,
    },
    case Star : re ih {
      unfold derive,
      rw [←heq, star_ne] at h,
      rcases h with ⟨s₀, s₁, rfl, h₁, h₂⟩,
      rw app_exists,
      refine ⟨s₀, s₁, rfl, _, h₂⟩,
      exact ih s₀ (a :: s₀) rfl h₁,
    },
  intro h,
  induction re generalizing s,
  case EmptySet { cases h, },
  case EmptyStr { cases h, },
  case Char {
    unfold derive at h,
    /- can't just use a = re -/
    cases (char.decidable_eq a re) with h' h',
      unfold ite at h,
      cases h,
    unfold ite at h,
    cases h,
    rw h',
    exact MChar re,
  },
  case App : re₁ re₂ ih₁ ih₂ {
    unfold derive at h,
    rw app_ne,
    cases hm : match_eps re₁,
      rw hm at h,
      simp only [bool.coe_sort_ff, if_false] at h,
      rcases app_exists.mp h with ⟨s₀, s₁, rfl, h₁, h₂⟩,
      exact or.inr ⟨s₀, s₁, rfl, ih₁ s₀ h₁, h₂⟩,
    rw hm at h,
    simp only [if_true, bool.coe_sort_tt] at h,
    rw union_disj at h,
    cases h,
      rcases app_exists.mp h with ⟨s₀, s₁, rfl, h₁, h₂⟩,
      exact or.inr ⟨s₀, s₁, rfl, ih₁ s₀ h₁, h₂⟩,
    have, exact match_eps_refl re₁,
    rw hm at this,
    cases this with this,
    exact or.inl ⟨this, ih₂ s h⟩,
  },
  case Union : re₁ re₂ ih₁ ih₂ {
    unfold derive at h,
    rw union_disj at h ⊢,
    cases h,
      exact or.inl (ih₁ s h),
    exact or.inr (ih₂ s h),
  },
  case Star : re ih {
    unfold derive at h,
    rcases app_exists.mp h with ⟨s₀, s₁, rfl, h₁, h₂⟩,
    rw star_ne,
    exact ⟨s₀, s₁, rfl, ih s₀ h₁, h₂⟩,
  },
end

/-
Definition matches_regex m : Prop :=
  ∀(s : string) re, reflect (s =~ re) (m s re).
-/

def matches_regex (m : list α → @reg_exp α → bool) :=
  ∀s re, reflect (s =~ re) (m s re)

/-
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def regex_match : str → @reg_exp char → bool
| [] r := match_eps r
| (c :: s) r := regex_match s (derive c r)

/-
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem regex_refl : matches_regex regex_match :=
begin
  unfold matches_regex,
  intros,
  induction s with a s ih generalizing re,
    exact match_eps_refl re,
  rw derive_corr,
  unfold regex_match,
  exact ih (derive a re),
end

end indprop