import tactic.basic
import tactic.omega
import .ch06_logic

/-
Inductive even : nat → Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).
-/

open nat

inductive even : ℕ → Prop
| ev_0 : even 0
| ev_ss (n : ℕ) (h : even n) : even (succ (succ n))

open even

/-
Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n → wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "wrong_ev" must have "n"
        as 1st argument in "wrong_ev 0". *)
-/

/- this explains a lot of behavior that we've seen so far -/

-- inductive wrong_ev (n : ℕ) : Prop
-- | wrong_ev_0 : wrong_ev 0
-- | wrong_ev_ss : wrong_ev n → wrong_ev (succ (succ n))

/-
  Inductive even : nat → Prop :=
  | ev_0 : even 0
  | ev_SS : ∀n, even n → even (S (S n)).
-/

inductive even' : ℕ → Prop
| ev_0 : even' 0
| ev_ss : ∀n, even' n → even' (succ (succ n))

/-
Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.
-/

theorem ev_4 : even 4 :=
begin
  apply ev_ss,
  apply ev_ss,
  exact ev_0,
end

/-
Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.
-/

theorem ev_4' : even 4 := ev_ss _ $ ev_ss _ ev_0

/-
Theorem ev_plus4 : ∀n, even n → even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.
-/

theorem ev_plus4 (n : ℕ) (h : even n) : even (4 + n) :=
begin
  rw add_comm,
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

theorem ev_double (n : ℕ) : even (double n) :=
begin
  induction n with n ih,
    simp [ev_0],
  simp,
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

theorem ev_inversion (n : ℕ) (h : even n)
  : (n = 0) ∨ (∃n', n = succ (succ n') ∧ even n') :=
begin
  cases h with n' h',
    left,
    refl,
  right,
  exact ⟨n', rfl, h'⟩,
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

theorem ev_minus (n : ℕ) (h : even n) : even (pred (pred n)) :=
begin
  cases h with n' h',
    simp,
    exact h,
  simp,
  exact h',
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

/- oh, cases is inversion, destruct is destruct... -/

-- theorem evss_ev (n : ℕ) (h : even (succ (succ n))) : even n :=
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

/- discriminate is injection, does not work here -/

theorem evss_ev (n : ℕ) (h : even (succ (succ n))) : even n :=
begin
  have h, exact ev_inversion _ h,
  cases h with h h,
    injection h,
  cases h with n' h,
  cases h with hl hr,
  injection hl with hl,
  injection hl with hl,
  rw hl,
  exact hr,
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

theorem evss_ev' (n : ℕ) (h : even (succ (succ n))) : even n :=
begin
  cases h with n' h',
  exact h',
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

/- yikes -/

theorem one_not_even : ¬even 1 :=
begin
  by_contra h,
  have h, exact ev_inversion 1 h,
  cases h with h h,
    simp at h,
    contradiction,
  cases h with n h,
  cases h with hl hr,
  injection hl with hl,
  injection hl,
end

theorem one_not_even' : ¬even 1 :=
begin
  by_contra h,
  cases h,
end

/-
Theorem SSSSev__even : ∀n,
  even (S (S (S (S n)))) → even n.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- gotta f around sometimes -/

theorem ssssev_even (n : ℕ) (h : even (succ (succ (succ (succ n)))))
  : even n :=
by repeat { exact h <|> cases h with h h }

/-
Theorem even5_nonsense :
  even 5 → 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem even5_nonsense (h : even 5) : 2 + 2 = 9 :=
by repeat { contradiction <|> cases h with h h }

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

/- does not appear to do injection -/

theorem inversion_ex₁ (n m o : ℕ) (h : [n, m] = [o, o])
  : [n] = [m] :=
begin
  cases h,
  injection h,
end

/- injection h also works... -/

theorem inversion_ex₂ (n : ℕ) (h : succ n = 0)
  : 2 + 2 = 5 := by cases h

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

-- lemma ev_evn_firstry (n : ℕ) (h : even n)
--   : ∃k, n = double k :=
-- begin
--   cases h with n' h',
--     exact ⟨0, rfl⟩,
--   have i : (∃k', n' = double k') →
--            (∃k, succ (succ n') = double k),
--     intro hk',
--     cases hk' with k' hk',
--     rw hk',
--     exact ⟨succ k', rfl⟩,
--     sorry
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

lemma ev_even (n : ℕ) (h : even n)
  : ∃k, n = double k :=
begin
  induction h with n' h' ih,
    exact ⟨0, rfl⟩,
  cases ih with k' hk',
  rw hk',
  exact ⟨succ k', rfl⟩,
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

/- mixing term and tactics, why not -/

theorem ev_even_iff (n : ℕ)
  : even n ↔ ∃k, n = double k :=
⟨ev_even n, begin
  intro h,
  cases h with k hk,
  rw hk,
  apply ev_double,
end⟩

/-
Theorem ev_sum : ∀n m, even n → even m → even (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem ev_sum (n m : ℕ) (hn : even n) (hm : even m) : even (n + m) :=
begin
  induction hn with n' hn' ih,
    simp *,
  simp,
  exact ev_ss _ ih,
end

/-
Inductive even' : nat → Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).
-/

inductive even'' : ℕ → Prop
| even''_0 : even'' 0
| even''_2 : even'' 2
| even''_sum n m (hn : even'' n) (hm : even'' m) : even'' (n + m)

open even''

/-
Theorem even'_ev : ∀n, even' n ↔ even n.
Proof.
 (* FILL IN HERE *) Admitted.
-/

/- 4* ? -/

theorem even''_ev (n : ℕ) : even'' n ↔ even n :=
begin
  split; intro h,
    induction h with n' m' hn' hm' ihn ihm,
        exact ev_0,
      exact ev_ss _ ev_0,
    exact ev_sum _ _ ihn ihm,
  induction h with n' hn' ih,
    exact even''_0,
  exact even''_sum _ _ ih even''_2,
end

/-
Theorem ev_ev__ev : ∀n m,
  even (n+m) → even n → even m.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem ev_ev__ev (n m) (hnm : even (n + m)) (hn : even n) : even m :=
begin
  induction hn with n' hn' ih,
    simp * at *,
  simp at hnm,
  exact ih (evss_ev _ hnm),
end

/-
Theorem ev_plus_plus : ∀n m p,
  even (n+m) → even (n+p) → even (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem ev_plus_plus (n m p) (hnm : even (n + m)) (hnp : even (n + p))
  : even (m + p) :=
begin
  have h₁, exact ev_sum _ _ hnm hnp,
  have : (n + m + (n + p)) = ((n + n) + (m + p)),
    ac_refl, /- sexy -/
  rw this at h₁,
  have h₂ : even (n + n),
    rw ←double_plus,
    apply ev_double,
  exact ev_ev__ev _ _ h₁ h₂,
end

/-
Inductive le : nat → nat → Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m ≤ n" := (le m n).
-/

inductive le : ℕ → ℕ → Prop
| le_n (n : ℕ) : le n n
| le_s {n m} (h : le n m) : le n (succ m)

open le

infix ` ≤' `:50 := le

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

theorem test_le₁ : 3 ≤' 3 := le_n 3

/-
yeah, as long as you define it right
this solves a lot
-/
theorem test_le₂ : 3 ≤' 6 := by repeat {constructor}

/-
TODO, need to figure out how to use case for naming
-/

theorem test_le₃ (h : 2 ≤' 1) : 2 + 2 = 5 :=
begin
  with_cases { cases h },
  case : h {
    cases h,
  },
end


/-
Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).
-/

def lt (n m) := le (succ n) m

infix ` <' `:50 := lt

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
| nn (n : ℕ) : next_nat n (succ n)

inductive next_even : ℕ → ℕ → Prop
| ne_1 (n : ℕ) : even (succ n) → next_even n (succ n)
| ne_2 (n) (h : even (succ (succ n))) : next_even n (succ (succ n))

inductive total_relation : ℕ → ℕ → Prop
| intro (n₁ n₂) : total_relation n₁ n₂

inductive empty_relation' : ℕ → ℕ → Prop

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

lemma le_trans' {m n o : ℕ} (hmn : m ≤' n) (hno : n ≤' o) : m ≤' o :=
begin
  induction hno with n' n' o' hno' ih,
    exact hmn,
  exact le_s (ih hmn),
end

theorem z_le_n (n : ℕ) : 0 ≤' n :=
begin
  induction n with n' ih,
    exact le_n 0,
  exact le_s ih,
end

theorem n_le_m__sn_le_sm {n m : ℕ} (h : n ≤' m) : succ n ≤' succ m :=
begin
  induction h with n' n' m' h' ih,
    constructor,
  exact le_s ih,
end

/- this sucked -/
/- why does induction destroy information -/

theorem sn_le_sm__n_le_m {n m : ℕ} (h : succ n ≤' succ m) : n ≤' m :=
begin
  cases h with n m n h',
    constructor,
  /-
  TODO - why tf can i not use case label renaming here
  -/
  exact le_trans' (le_s (le_n n)) h',
end

theorem le_plus_l (a b : ℕ) : a ≤' a + b :=
begin
  induction b with b' ihb,
    rw add_zero,
    constructor,
  exact le_s ihb,
end

theorem plus_lt {n₁ n₂ m} (h : n₁ + n₂ <' m) : n₁ <' m ∧ n₂ <' m :=
begin
  unfold lt at *,
  have : ∀ n m, succ n ≤' succ (n + m),
    intros n m,
    rw ←plus_Sn_m,
    exact le_plus_l _ _,
  split,
    exact le_trans' (this n₁ n₂) h,
  rw plus_comm at h,
  exact le_trans' (this n₂ n₁) h,
end

theorem ls_s {n m} (h : n <' m) : n <' succ m :=
begin
  unfold lt at *,
  exact le_s h,
end

/- so easy in function mode -/
/- need to get it to work in tactics -/
/- lol, not sure why that was hard -/

theorem leb_complete {n m} (h : n <=? m = tt) : n ≤' m :=
begin
  induction n with n' ih generalizing m,
    exact z_le_n m,
  cases m with m',
    simp at h,
    contradiction,
  simp at h,
  exact n_le_m__sn_le_sm (ih h)
end

/-
Theorem leb_correct : ∀n m,
  n ≤ m →
  n <=? m = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- honestly no real difference between n and m-/

theorem leb_correct {n m} (h : n ≤' m) : n <=? m = tt :=
begin
  induction m with m' ih generalizing n,
  cases h; refl,
  cases n; unfold leb,
  exact ih (sn_le_sm__n_le_m h),
end

theorem leb_correct' {n m} (h : n ≤' m) : n <=? m = tt :=
begin
  induction n with n' ih generalizing m,
    cases m; unfold leb,
  cases m,
    cases h,
  exact ih (sn_le_sm__n_le_m h),
end

/-
Theorem leb_true_trans : ∀n m o,
  n <=? m = true → m <=? o = true → n <=? o = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem leb_true_trans {n m o}
  (hnm : n <=? m = tt) (hmo : m <=? o = tt)
  : n <=? o = tt :=
leb_correct (le_trans' (leb_complete hnm) (leb_complete hmo))

/-
Theorem leb_iff : ∀n m,
  n <=? m = true ↔ n ≤ m.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- if you didn't do the last section -/
/- you're gonna have a bad time -/

theorem leb_iff {n m : ℕ} :
  n <=? m = tt ↔ n ≤' m :=
⟨leb_complete, leb_correct⟩

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
| c₂ {m n o} (h : R m n o) : R (succ m) n (succ o)
| c₃ {m n o} (h : R m n o) : R m (succ n) (succ o)
| c₄ {m n o} (h : R (succ m) (succ n) (succ (succ o))) : R m n o
| c₅ {m n o} (h : R m n o) : R n m o

open R

/-
Definition fR : nat → nat → nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem R_equiv_fR : ∀m n o, R m n o ↔ fR m n = o.
Proof.
(* FILL IN HERE *) Admitted.
-/

def fR := λ (m n : ℕ), m + n

lemma add_m_n_z : ∀ {m n}, m + n = 0 → m = 0 ∧ n = 0
| 0 0 h := ⟨rfl, rfl⟩
| (m + 1) _ h := by rw plus_Sn_m at h; contradiction

/-
recommended - tricky induction
make fun of coq destruction naming (for once)
-/

theorem R_equiv_fR {m n o : ℕ} : R m n o ↔ fR m n = o :=
begin
  split; intro h,
    induction h,
    case c₁ : { refl },
    case c₂ : m' n' o' h ih {
      unfold fR at *,
      rw plus_Sn_m,
      rw ih,
    },
    case c₃ : m' n' o' h ih {
      unfold fR at *,
      have : m' + succ n' = succ (m' + n'),
        refl,
      rw this,
      rw ih,
    },
    case c₄ : m' n' o' h ih {
      unfold fR at *,
      simp at ih,
      injection ih,
    },
    case c₅ : m' n' o' h ih {
      unfold fR at *,
      rwa add_comm,
    },
  induction o with o' ihm generalizing m n,
    unfold fR at h,
    have h, exact add_m_n_z h,
    rw [h.left, h.right],
    exact c₁,
  unfold fR at *,
  cases m,
    cases n,
      contradiction,
    injection h with h,
    exact c₃ (ihm h),
  rw plus_Sn_m at h,
  injection h with h,
  exact c₂ (ihm h),
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

inductive subseq : list ℕ → list ℕ → Prop
| em : subseq [] []
| cr {l₁ l₂} (n : ℕ) (h : subseq l₁ l₂) : subseq l₁ (n::l₂)
| cl {l₁ l₂} (n : ℕ) (h : subseq l₁ l₂) : subseq (n::l₁) (n::l₂)

open subseq

theorem subseq_refl (l : list ℕ) : subseq l l :=
begin
  induction l with h t ih,
    exact em,
  exact cl h ih,
end

open list

theorem subseq_app (l₁ l₂ l₃ : list ℕ) (h : subseq l₁ l₂)
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

/- i think i got lucky -/

theorem subseq_trans {l₁ l₂ l₃}
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
| c₁ : R' 0 []
| c₂ : ∀ n l, R' n l → R' (succ n) (n :: l)
| c₃ : ∀ n l, R' (succ n) l → R' n l

/-its a safe vec index-/

/-
Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).
-/

inductive reg_exp (α : Type) : Type
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

/-
we've hit a wall -
cases can't use exp_match with ++
list.append is not a constructor
seeing how far we can get with ropes
-/

-- inductive rope (α : Type)
-- | nil : rope
-- | cons (a : α) (r : rope) : rope
-- | app (r₁ r₂ : rope) : rope

-- open rope

-- infix ` ::' `:67  := cons
-- notation `[` l:(foldr `, ` (h t, cons h t) nil `]'`) := l
-- infix ` ++' `:65 := app

-- def append {α : Type} : rope α → rope α → rope α
-- | []' []' := []'
-- | []' r := r
-- | (h::'t) r := h::'(append t r)
-- | (h ++' t) r := append h (append t

-- instance {α : Type} : has_append (rope α) :=
-- ⟨append⟩

inductive exp_match {α : Type} : reg_exp α → list α → Prop
| MEmpty : exp_match EmptyStr []
| MChar (a : α) : exp_match (Char a) [a]
| MApp {s₁ re₁ s₂ re₂} (h₁ : exp_match re₁ s₁) (h₂ : exp_match re₂ s₂)
  : exp_match (App re₁ re₂) (s₁ ++ s₂)
| MUnionL {s₁ re₁} re₂ (h : exp_match re₁ s₁)
  : exp_match (Union re₁ re₂) s₁
| MUnionR re₁ {s₂ re₂} (h : exp_match re₂ s₂)
  : exp_match (Union re₁ re₂) s₂
| MStar0 (re : reg_exp α) : exp_match (Star re) []
| MStarApp {s₁ s₂ re}
  (h₁ : exp_match re s₁)
  (h₂ : exp_match (Star re) s₂)
  : exp_match (Star re) (s₁ ++ s₂)

open exp_match

/-
Notation "s =~ re" := (exp_match s re) (at level 80).
-/

infix ` =~ `:35 := exp_match

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

example : Char 1 =~ [1] := MChar 1

example : App (Char 1) (Char 2) =~ [1,2] :=
MApp (MChar 1) (MChar 2)

/-
Example reg_exp_ex3 : ¬([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.
-/

/- works due to swapping order -/

example : ¬(Char 1 =~ [1, 2]) :=
begin
  by_contra c,
  cases c,
end

/- can do cases on a variable -/
/-
this is the first compat break that made me
consider a forum post.
also had me reaching for coq to compare
-/

example : ¬(∃c, App (Char 1) (Char 2) =~ c ∧ c.length = 1) :=
begin
  by_contra c,
  cases c with w c,
  cases c with cl cr,
  /- not sure why i can't use case after -/
  cases cl with _ s₁ re₁ s₂ re₂ h₁ h₂,
  cases h₁,
  cases h₂,
  simp at cr,
  injection cr with c,
  contradiction,
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

def reg_exp_of_list {α} : list α → reg_exp α
| [] := EmptyStr
| (h::t) := App (Char h) (reg_exp_of_list t)

example : reg_exp_of_list [1,2,3] =~ [1,2,3] :=
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

lemma MStar1 {α s} {re : reg_exp α} (h : re =~ s)
  : Star re =~ s :=
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

lemma empty_is_empty {α} (s : list α) : ¬(EmptySet =~ s) :=
begin
  by_contra c,
  cases c,
end

lemma MUnion' {α} (s : list α) (re₁ re₂)
  (h : re₁ =~ s ∨ re₂ =~ s) : Union re₁ re₂ =~ s :=
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

/- In is actually in the logic chapter -/

open list

lemma MStar' {α} (ss) (re : reg_exp α) (h : ∀s, In s ss → re =~ s)
  : Star re =~ foldr append [] ss :=
begin
  induction ss with hd tl ih,
    dsimp only [foldr],
    exact MStar0 re,
  simp at *,
  have f : re =~ hd,
    have, exact h hd,
    simp at this,
    exact this,
  have g : Star re =~ foldr append nil tl,
    have : (∀ s, hd = s ∨ In s tl → re =~ s) → (∀ s, In s tl → re =~ s),
      intros h s h',
      have, exact h s,
      exact this (or.inr h'),
    exact ih (this h),
  exact MStarApp f g,
end

/-
Lemma reg_exp_of_list_spec : ∀T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 ↔ s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- the coq version for → is so much simpler -/

lemma reg_exp_of_list_spec {α} (s₁ s₂ : list α)
  : reg_exp_of_list s₂ =~ s₁ ↔ s₁ = s₂ :=
begin
  split,
    intro h,
    induction s₂ with h₂ t₂ ih₂ generalizing s₁,
      simp [reg_exp_of_list] at h,
      cases h,
      refl,
    simp [reg_exp_of_list] at h,
    generalize heq : App (Char h₂) (reg_exp_of_list t₂) = re',
    rw heq at h,
    cases h,
    all_goals { try { contradiction }},
    case MApp : s₁' re₁ s₂' re₂ h₁' h₂' {
      injection heq with h₁'' h₂'',
      rw ←h₂'' at h₂',
      rw ←h₁'' at h₁',
      cases h₁',
      simp,
      exact ih₂ _ h₂',
    },
  intro h,
  induction s₂ with h₂ t₂ ih₂ generalizing s₁,
    simp [reg_exp_of_list],
    rw h,
    exact MEmpty,
  simp [reg_exp_of_list],
  rw h,
  exact MApp (MChar h₂) (ih₂ t₂ rfl),
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

def re_chars {α} : reg_exp α → list α
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

theorem in_re_match {α} (s : list α) (re : reg_exp α) (a : α)
  (hm : re =~ s) (hi : In a s) : In a (re_chars re) :=
begin
  induction hm,
  case MEmpty { apply hi, },
  case MChar { apply hi, },
  case MApp : s₁ re₁ s₂ re₂ h₁ h₂ ih₁ ih₂ {
    dsimp only [re_chars],
    rw in_app_iff at *,
    exact or.imp ih₁ ih₂ hi,
  },
  case MUnionL : s₁ re₁ re₂ h ih {
    dsimp only [re_chars],
    rw in_app_iff,
    exact or.inl (ih hi),
  },
  case MUnionR : s₁ re₁ re₂ h ih {
    dsimp only [re_chars],
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

def re_not_empty {α} (re : reg_exp α) : bool :=
begin
  induction re,
  case EmptySet { exact ff, },
  case EmptyStr { exact tt, },
  case Char { exact tt, },
  case App : re₁ re₂ ih₁ ih₂ { exact ih₁ && ih₂, },
  case Union : re₁ re₂ ih₁ ih₂ { exact ih₁ || ih₂, },
  case Star { exact tt, },
end

lemma re_not_empty_correct {α} (re : reg_exp α)
  : (∃s, re =~ s) ↔ re_not_empty re = tt :=
begin
  split; intro h,
    /- braces so all_goals doesn't affect other direction -/
    cases h with w h, {
    induction h,
      /- dsimp breaks cases. rw and simp don't -/
      all_goals { rw [re_not_empty], },
      case MApp : s₁ re₁ s₂ re₂ h₁ h₂ ih₁ ih₂ {
        rw [band_eq_true_eq_eq_tt_and_eq_tt],
        show re_not_empty re₁ = tt ∧ re_not_empty re₂ = tt,
        exact ⟨ih₁, ih₂⟩,
      },
      all_goals { rw [bor_eq_true_eq_eq_tt_or_eq_tt], },
      case MUnionL : s₁ re₁ re₂ h ih {
        show re_not_empty re₁ = tt ∨ re_not_empty re₂ = tt,
        exact or.inl ih,
      },
      case MUnionR : re₁ s₂ re₂ h ih {
        show re_not_empty re₁ = tt ∨ re_not_empty re₂ = tt,
        exact or.inr ih,
      },
    },
  induction re,
  all_goals { rw [re_not_empty] at h, },
  case EmptySet { contradiction, },
  case EmptyStr { exact ⟨[], MEmpty⟩, },
  case Char { exact ⟨[re], MChar re⟩, },
  case App : re₁ re₂ ih₁ ih₂ {
    rw [band_eq_true_eq_eq_tt_and_eq_tt] at h,
    change re_not_empty re₁ = tt ∧ re_not_empty re₂ = tt at h,
    cases (ih₁ h.left) with w₁ ih₁,
    cases (ih₂ h.right) with w₂ ih₂,
    exact ⟨w₁ ++ w₂, MApp ih₁ ih₂⟩,
  },
  case Union : re₁ re₂ ih₁ ih₂ {
    rw [bor_eq_true_eq_eq_tt_or_eq_tt] at h,
    change re_not_empty re₁ = tt ∨ re_not_empty re₂ = tt at h,
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

-- lemma star_app {α} (s₁ s₂ : list α) (re)
--   (h₁ : Star re =~ s₁) (h₂ : Star re =~ s₂)
--   : Star re =~ s₁ ++ s₂ :=
-- begin
--   induction h₁,
--   { simp, exact h₂, },
-- end

/-
Lemma star_app: ∀T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re →
  s1 =~ re' →
  s2 =~ Star re →
  s1 ++ s2 =~ Star re
Abort.
-/

-- lemma star_app {α} (s₁ s₂ : list α) (re) {re'}
--   {heq : Star re = re'}
--   (h₁ : Star re =~ s₁)
--   (h₂ : Star re =~ s₂)
--   : Star re =~ s₁ ++ s₂ :=
-- begin
--   sorry
-- end

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

lemma star_app {α} (s₁ s₂ : list α) (re)
  (h₁ : Star re =~ s₁)
  (h₂ : Star re =~ s₂)
  : Star re =~ s₁ ++ s₂ :=
begin
  /- order freaking matters -/
  revert re,
  intro,
  generalize heq : Star re = re',
  intros,
  induction h₁ generalizing h₂,
  all_goals { try { contradiction } },
  case MStar0 { exact h₂, },
  case MStarApp : s₁' s₂' re' h₁' h₂' ih₁ ih₂ {
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

/-
had an existential that was close but wrong
it didn't relate to the witness and it led
to tricky issues
also, this is the first time i used apply exists.intro
instead of exact ⟨...⟩
-/

lemma MStar'' {α} {s : list α} {re}
  (h : Star re =~ s)
  : ∃ss, s = foldr append [] ss
    ∧ ∀ {s'}, In s' ss → re =~ s' :=
begin
  revert h,
  generalize heq : Star re = re',
  intro,
  induction h,
  all_goals { try { contradiction } },
  case MStar0 : re' { exact ⟨[], by simp⟩, },
  case MStarApp : s₁ s₂ re' h₁ h₂ ih₁ ih₂ {
    cases ih₂ heq with w h,
    apply exists.intro (s₁::w),
    cases h with hl hr,
    rw hl,
    simp,
    intros s' h',
    cases h',
      injection heq with heq',
      rw heq',
      rwa ←h',
    exact hr h',
  },
end

lemma MStar''' {α} {s : list α} {re}
  : ∀ (h : Star re =~ s),
    ∃ss, s = foldr append [] ss
    ∧ ∀ {s'}, In s' ss → re =~ s' :=
begin
  generalize heq : Star re = re',
  intro,
  induction h,
  all_goals { try { contradiction } },
  case MStar0 : re' { exact ⟨[], by simp⟩, },
  case MStarApp : s₁ s₂ re' h₁ h₂ ih₁ ih₂ {
    cases ih₂ heq with w h,
    exact ⟨s₁::w, by {
      cases h with hl hr,
      rw hl,
      simp,
      intros s' h',
      cases h',
        injection heq with heq',
        rw heq',
        rwa ←h',
      exact hr h',
    }⟩
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

def pumping_constant {α} : reg_exp α → ℕ
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

def napp {α} : ℕ → list α → list α
| 0 _ := []
| (n + 1) l := l ++ napp n l

lemma napp_plus {α} (n m) (l : list α)
  : napp (n + m) l = napp n l ++ napp m l :=
begin
  induction n with n ih,
    simp [napp],
  simp [napp],
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

-- lemma pumping {α} {re : reg_exp α} {s}
--   (hm : re =~ s)
--   (hp : pumping_constant re ≤ length s)
--   : ∃ {s₁ s₂ s₃},
--     s = s₁ ++ s₂ ++ s₃ ∧
--     s₂ ≠ [] ∧
--     ∀ {m}, re =~ s₁ ++ napp m s₂ ++ s₃ :=
-- begin
--   induction hm,
--   case MEmpty {
--     simp at hp,
--     /- omega doesn't work here, but not sure why it'd be needed -/
--     contradiction,
--   },
--   all_goals { sorry, },
-- end

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

theorem filter_not_empty_In {n l}
  (h : filter (λ x, n =? x) l ≠ [])
  : In n l :=
begin
  induction l with m l ih,
    simp at h,
    contradiction,
  simp,
  cases heq : (n =? m),
    right,
    apply ih,
    simp [filter] at h,
    rwa heq at h,
  left,
  rw eqb_eq at heq,
  symmetry,
  exact heq,
end

/-
Inductive reflect (P : Prop) : bool → Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ¬P) : reflect P false.
-/

/- not really sure what the builtin one is-/
inductive reflect' (P : Prop) : bool → Prop
| ReflectT (h : P) : reflect' tt
| ReflectF (h : ¬P) : reflect' ff

open reflect'

/-
Theorem iff_reflect : ∀P b, (P ↔ b = true) → reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.
-/

theorem iff_reflect {P b} (h : P ↔ b = tt) : reflect' P b :=
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

theorem reflect_iff {P b} (h : reflect' P b) : (P ↔ b = tt) :=
begin
  cases h with h' h',
    simp,
    exact h',
  simp,
  exact h',
end

/-
Lemma eqbP : ∀n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.
-/

lemma eqbP (n m) : reflect' (n = m) (n =? m) :=
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

/- complaint below is invalid with generalize -/
-- /- can't use cases, and destruct is bad -/
-- /- this is much worse than without ebqP -/

theorem filter_not_empty_In' {n l}
  (h : filter (λ x, n =? x) l ≠ [])
  : In n l :=
begin
  induction l with m l' ih,
    simp at h,
    contradiction,
  simp,
  have, exact eqbP n m,
  generalize heq : n =? m = eq,
  generalize heq' : n = m = eq',
  rw [heq, heq'] at this,
  cases this,
  case ReflectT : this' {
    rw ←heq' at this',
    rw this',
    exact or.inl (refl _),
  },
  case ReflectF : this' {
    unfold filter at h,
    rw heq at h,
    simp at h,
    exact or.inr (ih h),
  },
end

-- theorem filter_not_empty_In' {n l}
--   (h : filter (λ x, n =? x) l ≠ [])
--   : In n l :=
-- begin
--   induction l with m l' ih,
--     simp at h,
--     contradiction,
--   simp,
--   simp [filter] at h,
--   destruct (eqbP n m),
--     intro h',
--     left,
--     symmetry,
--     exact h',
--   intro h',
--   right,
--   apply ih,
--   have : n =? m = ff,
--     rwa eqb_neq,
--   rw this at h,
--   simp at h,
--   exact h,
-- end

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

def count' (n) : list ℕ → ℕ
| [] := 0
| (m::l) := (if n =? m then 1 else 0) + count' l

theorem eqbP_practice {n l}
  (h : count' n l = 0)
  : ¬In n l :=
begin
  induction l with m t ih,
    simp,
  simp [count'] at h,
  cases heq : (n =? m),
    simp,
    by_contra c,
    rw heq at h,
    simp at h,
    cases c,
      have : n =? m = tt,
        rw c,
        simp,
      rw heq at this,
      contradiction,
    exact absurd c (ih h),
  rw heq at h,
  simp at h,
  contradiction,
end

/- still not better. should see what coq does -/
/- even after learning generalize, it's not great -/

theorem eqbP_practice' {n l}
  (h : count' n l = 0)
  : ¬In n l :=
begin
  induction l with m t ih,
    simp,
  simp [count'] at h,
  generalize heq : n = m = eq,
  generalize heq' : n =? m = eq',
  have, exact eqbP n m,
  rw [heq, heq'] at this,
  cases this,
  case ReflectT : this' {
    rw heq' at h,
    simp at h,
    contradiction,
  },
  case ReflectF : this' {
    rw heq' at h,
    simp at h,
    simp,
    by_contra c,
    cases c,
      rw [←heq, c] at this',
      contradiction,
    exact absurd c (ih h),
  },
end

-- theorem eqbP_practice' {n l}
--   (h : count' n l = 0)
--   : ¬In n l :=
-- begin
--   induction l with m t ih,
--     simp,
--   simp [count'] at h,
--   destruct (eqbP n m),
--     intro heq,
--     simp,
--     rw heq at h,
--     simp at h,
--     contradiction,
--   intro heq,
--   have : n =? m = ff,
--     exact (eqb_neq n m).mpr heq,
--   rw this at h,
--   simp,
--   simp at h,
--   by_contra c,
--   cases c,
--     rw c at heq,
--     contradiction,
--   exact absurd c (ih h),
-- end

/-
Inductive nostutter {X:Type} : list X → Prop :=
 (* FILL IN HERE *)
.
-/

inductive nostutter {α : Type} : list α → Prop
| no₀ : nostutter []
| no₁ (a) : nostutter [a]
| no₂ (a) {h t} (n : nostutter (h::t)) (hne : a ≠ h)
  : nostutter (a::h::t)

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

example : nostutter [3,1,4,1,5,6] :=
begin
  repeat { constructor },
  repeat {
    simp,
    by_contra c,
    cases c,
  },
end

example : @nostutter ℕ [] := no₀

example : nostutter [5] := no₁ 5

example : ¬nostutter [3,1,1,4] :=
begin
  by_contra c,
  repeat {
    cases c with _ _ _ _ c h,
    try { trivial },
  },
end

inductive merge {α} : list α → list α → list α → Prop
| m₀ : merge [] [] []
| ml (h) {t r m} (hm : merge t r m) : merge (h::t) r (h::m)
| mr {l} (h) {t m} (hm : merge l t m) : merge l (h::t) (h::m)

open merge

example : merge [1,2,3] [4,5,6] [1,2,3,4,5,6] :=
by repeat { constructor }

example : merge [1,2,3] [4,5,6] [4,5,6,1,2,3] :=
by repeat { constructor }

example : merge [1,2,3] [4,5,6] [1,4,2,5,3,6] :=
by repeat { constructor }

open poly

lemma filter_merge {α} {l r m} {p : α → bool}
  (hm : merge l r m)
  (hf : ∀a, In a l → p a = ff)
  (ht : ∀a, In a r → p a = tt)
  : filter p m = r :=
begin
  induction hm,
  case m₀ { refl, },
  case ml : h t r m hm ih {
    have : p h = ff,
      apply hf,
      simp,
    simp,
    rw this,
    simp,
    apply ih,
      intros a hin,
      simp at hf,
      exact hf a (or.inr hin),
    intros a hin,
    exact ht a hin,
  },
  case mr : l h t m hm ih {
    have : p h = tt,
      apply ht,
      simp,
    simp,
    rw this,
    simp,
    apply ih,
      intros a hin,
      exact hf a hin,
    intros a hin,
    simp at ht,
    exact ht a (or.inr hin),
  },
end

/-
TODO filter challenge 2
-/

/- revenge of the lst -/
/- pretty easy -/
/- probably due to lots of simp attributes -/

inductive pal {α} : lst α → Prop
| pal₀ : pal ⟦⟧
| pal₁ (a) : pal ⟦a⟧
| pal₂ (a) {l} (h : pal l) : pal (a::l ++ ⟦a⟧)

open pal

example : pal ⟦1,2,1⟧ :=
begin
  have : (⟦1,2,1⟧ : lst ℕ) = (⟦1,2⟧ : lst ℕ) ++ (⟦1⟧ : lst ℕ),
    refl,
  rw this,
  repeat {constructor},
end

lemma pal_app_rev {α} (l : lst α) : pal (l ++ rev l) :=
begin
  induction l with h t ih,
    simp,
    exact pal₀,
  simp,
  rw app_assoc,
  exact pal₂ h ih,
end

lemma pal_rev {α} {l : lst α} (p : pal l) : l = rev l :=
begin
  induction p,
  case pal₀ { refl, },
  case pal₁ { refl, },
  case pal₂ : h t hp ih {
    simp,
    rw ←ih,
  },
end

/-
TODO palindrome_converse
-/

/- builtin has a nice alternative -/

inductive disjoint' {α} : list α → list α → Prop
| dis₀ : disjoint' [] []
| disl (h) {t r} (d : disjoint' t r) (hn : ¬In h r) : disjoint' (h::t) r
| disr (h) {l t} (d : disjoint' l t) (hn : ¬In h l) : disjoint' l (h::t)

open disjoint'

/- lean's builtin has a sweet definition -/

inductive nodup' {α} : list α → Prop
| nodup₀ : nodup' []
| nodup₁ (h) {l} (n : nodup' l) (hn : ¬In h l) : nodup' (h::l)

open nodup'

example : nodup' [1,2,3,4] :=
begin
  repeat {constructor},
  repeat {simp, try {omega} },
end

example : @nodup' bool [] := nodup₀

example : ¬nodup' [1,2,1] :=
begin
  by_contra c,
  cases c with _ _ h hn,
  simp at hn,
  contradiction,
end

example : ¬nodup' [tt,tt] :=
begin
  by_contra c,
  cases c with _ _ n hn,
  simp at hn,
  contradiction,
end

lemma in_append {α a} {l r : list α}
  : In a (l ++ r) ↔ In a l ∨ In a r :=
begin
  split,
    intro hin,
    induction l with h t ih,
      simp at hin,
      exact or.inr hin,
    simp,
    simp at hin,
    cases hin,
      exact or.inl (or.inl hin),
    rw or.assoc,
    exact or.inr (ih hin),
  intro hin,
  cases hin,
    induction l with h t ih,
      simp at hin,
      contradiction,
    simp,
    simp at hin,
    cases hin,
      exact or.inl hin,
    exact or.inr (ih hin),
  induction l with h t ih,
    simp,
    exact hin,
  simp,
  exact or.inr ih,
end

/- mfer -/

lemma dis_cons' {α} {a : α} {l r} (h : list.disjoint (a :: l) r)
  : ¬a ∈ r ∧ disjoint l r :=
begin
  simp [list.disjoint] at *,
  exact h,
end

lemma nil_dis {α} (l : list α) : disjoint' l nil :=
begin
  induction l with h t ih,
    exact dis₀,
  apply disl h ih,
  simp,
end

lemma dis_nil {α} (r : list α) : disjoint' nil r :=
begin
  induction r with h t ih,
    exact dis₀,
  apply disr h ih,
  simp,
end

lemma dis_iso {α} (l r : list α)
  : disjoint' l r ↔ (∀a, In a l → ¬In a r) ∧ (∀a, In a r → ¬In a l) :=
begin
  split,
    intro h,
    induction h,
    case dis₀ { simp, },
    case disl : h' t r' d hn ih {
      simp,
      constructor,
        cases ih with ihl ihr,
        intros a h'',
        cases h'',
          rwa h'' at hn,
        by_contra c,
        exact absurd h'' (ihr _ c),
      cases ih with ihl ihr,
      intros a h'',
      by_contra c,
      cases c,
        rw c at hn,
        contradiction,
      exact absurd h'' (ihl _ c),
    },
    case disr : h' l' t d hn ih {
      simp,
      constructor,
        cases ih with ihl ihr,
        intros a h'',
        by_contra c,
        cases c,
          rw c at hn,
          contradiction,
        exact absurd h'' (ihr _ c),
      cases ih with ihl ihr,
      intros a h'',
      cases h'',
        rwa h'' at hn,
      by_contra c,
      exact absurd h'' (ihl _ c),
    },
  intro h,
  cases h with hl hr,
  induction l with hd tl ih generalizing r,
    exact dis_nil r,
  simp at hl,
  simp at hr,
  have : disjoint' tl r,
    apply ih,
      intros a h',
      exact hl a (or.inr h'),
    intros a h',
    have, exact hr a h',
    rw not_or_distrib at this,
    cases this with hl' hr',
    exact hr',
  refine disl hd this _,
  apply hl,
  simp,
end

/- could not get this without dis_iso helper -/

lemma dis_cons {α} {h : α} {t r} (d : disjoint' (h :: t) r)
  : ¬In h r ∧ disjoint' t r :=
begin
  rw dis_iso (h::t) r at d,
  simp at d,
  cases d with dl dr,
  constructor,
    by_contra,
    have, exact dr h a,
    rw not_or_distrib at this,
    simp at this,
    contradiction,
  rw dis_iso t r,
  constructor,
    intros a h',
    apply dl,
    exact or.inr h',
  intros a h',
  have, exact dr a h',
  rw not_or_distrib at this,
  exact this.right,
end

lemma nodup_cons {α} {a : α} {l} (hn : nodup' (a::l)) : nodup' l :=
begin
  cases hn with _ _ n hn,
  exact n,
end

lemma nodup_app {α} {l r : list α} (hn : nodup' (l++r))
  : nodup' l ∧ nodup' r :=
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
    rw in_append at hn,
    rw not_or_distrib at hn,
    exact hn.left,
  }
end

lemma app_disjoint {α} {l r : list α}
  (hl : nodup' l) (hr : nodup' r)
  (hd : disjoint' l r)
  : nodup' (l ++ r) :=
begin
  rw dis_iso at hd,
  cases hd with hdl hdr,
  induction hl generalizing r,
  case nodup₀ {
    simp,
    exact hr,
  },
  case nodup₁ : h t n hn ih {
    simp,
    simp at hdl,
    simp at hdr,
    have : nodup' (t ++ r),
      apply ih hr,
        intros a h',
        exact hdl a (or.inr h'),
      intros a h',
      by_contra c,
      have, exact hdr a h',
      rw not_or_distrib at this,
      exact absurd c this.right,
    refine nodup₁ h this _,
    by_contra c,
    rw in_append at c,
    cases c,
      contradiction,
    have : ¬In h r,
      apply hdl h,
      simp,
    contradiction,
  },
end


/- not an iso because i forget order -/

lemma merge_iso' {α} {l r m : list α} (h : merge l r m)
  : length m = length l + length r ∧
  ∀a, In a m ↔ In a l ∨ In a r :=
begin
  induction h,
  case m₀ { simp, },
  case ml : h t r' m hm ih {
    cases ih with ihl ihr,
    simp,
    split,
      rw ihl,
    intro a,
    split,
      intro h',
      cases h',
        exact or.inl (or.inl h'),
      rw or_assoc,
      exact or.inr ((ihr a).mp h'),
    intro h',
    rw or_assoc at h',
    cases h',
      exact or.inl (h'),
    exact or.inr ((ihr a).mpr h'),
  },
  case mr : l' h t m' hm ih {
    cases ih with ihl ihr,
    simp,
    split,
      rw ihl,
      rw add_assoc,
    intro a,
    split,
      intro h',
      cases h',
        exact or.inr (or.inl h'),
      rw [←or_assoc, or_comm (In a l'), or_assoc],
      exact or.inr ((ihr a).mp h'),
    intro h',
    cases h',
      exact or.inr ((ihr a).mpr (or.inl h')),
    cases h',
      exact or.inl h',
    exact or.inr ((ihr a).mpr (or.inr h')),
  },
end

-- lemma merge_order {α} : ∀ {l r m : list α} (h : merge l r m),
--   ∀{l₁ l₂}, l = l₁ ++ l₂ →
--     ∃r₁ r₂, r = r₁ ++ r₂ ∧
--       ∃m₁ m₂, m = m₁ ++ m₂ ∧
--         merge l₁ r₁ m₁ ∧
--         merge l₂ r₂ m₂
-- | l r m (m₀) :=
-- begin
--   intros _ _ heq,
--   exact ⟨[], [], by {
--     simp,
--     exact ⟨[], [], by {
--       simp,
--       simp at heq,
--       cases heq with h₁ h₂,
--       rw [h₁, h₂],
--       exact ⟨m₀, m₀⟩,
--     }⟩,
--   }⟩,
-- end
-- | (h₁::t₁) r (m₁::m₂) (ml h m) :=
-- begin
--   intros _ _ heq,
--   cases l₁ with h₁' t₁',
--     sorry,
--   injection heq with hl hr,
--   have, exact merge_order m hr,
--   cases this with wr₁ h',
--   cases h' with wr₂ h',
--   cases h' with hl' hr',
--   cases hr' with wm₁ hr',
--   cases hr' with wm₂ hr',
--   exact ⟨wr₁, wr₂, by {
--     split,
--       exact hl',
--     exact ⟨h::wm₁, wm₂, by {
--       simp,
--       rw ←hl,
--       exact ⟨hr'.left, ml h hr'.right.left, hr'.right.right⟩,
--     }⟩,
--   }⟩,
-- end
-- | l (h₂::t₂) (m₁::m₂) (mr h m) :=
-- begin
--   sorry,
-- end

-- lemma merge_order {α} {l r m : list α} (h : merge l r m)
--   : ∀{l₁ l₂}, l = l₁ ++ l₂ →
--     ∃r₁ r₂, r = r₁ ++ r₂ ∧
--       ∃m₁ m₂, m = m₁ ++ m₂ ∧
--         merge l₁ r₁ m₁ ∧
--         merge l₂ r₂ m₂ :=
-- begin
--   induction m generalizing l r,
--   case nil {
--     cases h,
--     simp,
--     intros _ _ h₁ h₂,
--     exact ⟨[], [], by {
--       simp,
--       exact ⟨[], [], by {
--         simp,
--         rw [h₁, h₂],
--         exact ⟨m₀, m₀⟩,
--       }⟩,
--     }⟩,
--   },
--   case cons : hd tl ih {
--     cases h,
--     case ml : t hm {
--       intros _ _ heq,
--       cases l₁ with h₁ t₁,
--         cases l₂ with h₂ t₂,
--           cases heq,
--         injection heq with hl hr,
--         rw ←nil_append t₂ at hr,
--         have, exact ih hm hr,
--         cases this with wr₁ h',
--         cases h' with wr₂ h',
--         cases h' with hl' hr',
--         cases hr' with wm₁ hr',
--         cases hr' with wm₂ hr',
--         exact ⟨wr₁, wr₂, by {
--           split,
--             exact hl',
--           exact ⟨hd::wm₁, wm₂, by {
--             simp,
--             rw ←hl,
--             sorry,
--             -- exact ⟨hr'.left, ml hd hr'.right.left, hr'.right.right⟩,
--           }⟩
--         }⟩,
--       injection heq with hl hr,
--       have, exact ih hm hr,
--       cases this with wr₁ h',
--       cases h' with wr₂ h',
--       cases h' with hl' hr',
--       cases hr' with wm₁ hr',
--       cases hr' with wm₂ hr',
--       exact ⟨wr₁, wr₂, by {
--         split,
--           exact hl',
--         exact ⟨hd::wm₁, wm₂, by {
--           simp,
--           rw ←hl,
--           exact ⟨hr'.left, ml hd hr'.right.left, hr'.right.right⟩,
--         }⟩
--       }⟩
--     }
--   }
-- end

-- lemma merge_order {α} {l r m : list α} (h : merge l r m)
--   : ∀l₁ l₂, l = l₁ ++ l₂ →
--     ∃r₁ r₂ m₁ m₂,
--       r = r₁ ++ r₂ ∧
--       m = m₁ ++ m₂ ∧
--       merge l₁ r₁ m₁ ∧
--       merge l₂ r₂ m₂ :=
-- begin
--   induction h,
--   case m₀ {
--     simp,
--     intros _ _ hl₁ hl₂,
--     exact ⟨[], [], ⟨rfl, rfl⟩, [], [], by {
--       simp,
--       rw [hl₁, hl₂],
--       exact ⟨m₀, m₀⟩,
--     }⟩
--   },
--   case ml : h t r' m hm ih {
--     simp at *,
--     intros _ _ hl,
--     cases l₁ with h₁ t₁,
--       simp at hl,
--       cases l₂ with h₂ t₂,
--         contradiction,
--       injection hl with hll hlr,
--       have, exact ih [] t₂ hlr,
--       cases this with wr₁ h',
--       cases h' with wr₂ h',
--       cases h' with hl' hr',
--       cases hr' with wm₁ hr',
--       cases hr' with wm₂ hr',
--       exact ⟨wr₁, wr₂, by {
--         split,
--           exact hl',
--         exact ⟨wm₁, h::wm₂, by {
--           simp,
--           sorry,
--         }⟩,
--       }⟩,
--     injection hl with hll hlr,
--     have, exact ih t₁ l₂ hlr,
--     cases this with wr₁ h',
--     cases h' with wr₂ h',
--     cases h' with hl' hr',
--     cases hr' with wm₁ hr',
--     cases hr' with wm₂ hr',
--     exact ⟨wr₁, wr₂, by {
--       split,
--         exact hl',
--       exact ⟨h::wm₁, wm₂, by {
--         simp,
--         rw ←hll,
--         exact ⟨hr'.left, ml h hr'.right.left, hr'.right.right⟩,
--       }⟩
--     }⟩
--   },
--   case mr : l' h t m' hm ih {

--   },
-- end

/- i have literally no clue why explicit type is needed here -/

lemma merge_nil {α : Type} {r m : list α} (h : merge nil r m) : r = m :=
begin
  have, exact merge_iso' h,
  induction r generalizing m,
  case nil {
    induction m with hd tl ih,
      refl,
    simp at this,
    contradiction,
  },
  case cons : hd tl ih {
    cases h with _ _ _ _ _ _ _ _ m hm,
    have hm', exact merge_iso' hm,
    cases hm' with hml hmr,
    cases this with hl hr,
    simp at *,
    exact ih hm hl hmr,
  },
end

-- lemma merge_disjoint {α} {l r m: list α}
--   (hl : nodup' l) (hr : nodup' r)
--   (hd : disjoint' l r)
--   (hm : merge l r m)
--   : nodup' m :=
-- begin
--   rw dis_iso at hd,
--   have hm', exact merge_iso' hm,
--   cases hd with hdl hdr,
--   induction l with h t ih generalizing r m,
--   case nil {
--     simp at hm',
--     induction hr,
--   }
-- end

-- lemma merge_disjoint {α} {l r m: list α}
--   (hl : nodup' l) (hr : nodup' r)
--   (hd : disjoint' l r)
--   (hm : merge l r m)
--   : nodup' m :=
-- begin
--   rw dis_iso at hd,
--   cases hd with hdl hdr,
--   induction hm,
--   case m₀ { exact nodup₀, },
--   case ml : h t r' m' hm' ih {
--     simp at hdl,
--     simp at hdr,
--     have : nodup' m',
--       apply ih (nodup_cons hl) hr,
--         intro a,
--         exact (or_imp_distrib.mp (hdl a)).right,
--       intros a h',
--       exact (not_or_distrib.mp (hdr a h')).right,
--     refine nodup₁ h this _,
--     by_contra c,

--   },
-- end

-- lemma merge_disjoint' {α} {l r m: list α}
--   (hl : nodup' l) (hr : nodup' r)
--   (hd : disjoint' l r)
--   (hm : merge l r m)
--   : nodup' m :=
-- begin
--   rw dis_iso at hd,
--   cases hd with hdl hdr,
--   induction m generalizing l r,
--   case nil { exact nodup₀, },
--   case cons : hd tl ih {
--     cases hm,
--     case ml : t hm' {
--       have : nodup' tl,
--         apply ih (nodup_cons hl) hr hm',
--           simp at hdl,
--           intro a,
--           exact (or_imp_distrib.mp (hdl a)).right,
--         simp at hdr,
--         intros a h',
--         exact (not_or_distrib.mp (hdr a h')).right,
--       refine nodup₁ hd this _,
--       by_contra c,

--     }
--   }
-- end


lemma dis_swap {α} {l r : list α} (d : disjoint' l r) : disjoint' r l :=
begin
  induction d,
  case dis₀ { exact dis₀, },
  case disl : h t d d hn ih { exact disr h ih hn, },
  case disr : h l t d hn ih { exact disl h ih hn, },
end

lemma dis_swap' {α} {l r : list α} (d : disjoint' l r) : disjoint' r l :=
begin
  rw [dis_iso] at *,
  rwa and_comm,
end

/- that was an 'entertaining' detour -/

/-
Lemma in_split : ∀(X:Type) (x:X) (l:list X),
  In x l →
  ∃l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma in_split {α} (a : α) (l) (hin : In a l)
  : ∃l₁ l₂, l = l₁ ++ a :: l₂ :=
begin
  induction l with h t ih,
    cases hin,
  cases hin,
    exact ⟨[], t, by {
      simp,
      exact hin,
    }⟩,
  have, exact ih hin,
  cases this with w₁ h₁,
  cases h₁ with w₂ h₂,
  exact ⟨h::w₁, w₂, by {
    simp,
    exact h₂,
  }⟩,
end

/-
Inductive repeats {X:Type} : list X → Prop :=
  (* FILL IN HERE *)
.
-/

inductive repeats {α} : list α → Prop
| r₀ {a} {l} (hin : In a l) : repeats (a::l)
| r₁ (a) {l} (r : repeats l) : repeats (a::l)

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

section

/-
use the split helper and this is easy
forget about it, and you're gonna have a bad time
-/

open classical

theorem pigeonhole_principle {α} {l₁ l₂ : list α}
  (hin : ∀a, In a l₁ → In a l₂)
  (hlen : length l₂ < length l₁)
  : repeats l₁ :=
begin
  induction l₁ with h₁ t₁ ih generalizing l₂,
    cases hlen,
  cases l₂ with h₂ t₂,
    have, exact hin h₁,
    simp at this,
    contradiction,
  simp at hlen,
  cases (em (In h₁ t₁)) with h₁t₁ h₁t₁,
    exact r₀ h₁t₁,
  have : repeats t₁,
    have l₂', exact in_split h₁ (h₂::t₂),
    simp at hin,
    have, exact l₂' (hin h₁ (or.inl (refl _))),
    cases this with h₂' this,
    cases this with t₂' heq,
    apply @ih (h₂' ++ t₂'),
      show ∀a, In a t₁ → In a (h₂' ++ t₂'),
      intros a hin',
      have, exact hin a (or.inr hin'),
      cases this,
        cases h₂' with hh ht,
          injection heq with heq₁ heq₂,
          rw [←this, heq₁] at hin',
          contradiction,
        injection heq with heq₁ heq₂,
        rw [←this, ←heq₁],
        simp,
      cases h₂' with hh ht,
        injection heq with heq₁ heq₂,
        rw ←heq₂,
        simp,
        exact this,
      injection heq with heq₁ heq₂,
      rw heq₂ at this,
      change In a (ht  ++  (h₁::t₂')) at this,
      rw in_app_iff at this,
      rw in_app_iff,
      cases this,
        simp,
        exact or.inl (or.inr this),
      simp at this,
      cases this,
        have hn₁ : ¬a = h₁,
          by_contra c,
          rw c at hin',
          contradiction,
        rw this at hn₁,
        contradiction,
      exact or.inr this,
    show length (h₂' ++ t₂') < length t₁,
    have hlen', exact congr_arg list.length heq,
    have : length (h₂' ++ h₁ :: t₂') = length (h₂' ++ t₂') + 1,
      repeat {rw app_length},
      simp [add_assoc],
    rw this at hlen',
    injection hlen' with hlen'',
    simp at hlen'',
    rwa ←hlen'',
  exact r₁ h₁ this,
end

/-
TODO - don't use classical
-/

end

/-
Require Export Coq.Strings.Ascii.
Definition string := list ascii.
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

lemma provable_equiv_true {P : Prop} (p : P) : P ↔ tt :=
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

lemma not_equiv_false {P : Prop} (np : ¬P) : (P ↔ ff) :=
begin
  split,
    intro,
    contradiction,
  intro,
  contradiction,
end

/-
Lemma null_matches_none : ∀(s : string), (s =~ EmptySet) ↔ False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.
-/

lemma null_matches_none (s : str) : EmptySet =~ s ↔ ff :=
begin
  apply not_equiv_false,
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

lemma empty_matches_eps (s : str) : EmptyStr =~ s ↔ s = [] :=
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

lemma empty_nomatch_ne (a : char) (s) : EmptyStr =~ a::s ↔ ff :=
begin
  apply not_equiv_false,
  by_contra c,
  cases c,
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

lemma char_nomatch_char {a b} (s : str) (hne : b ≠ a)
  : Char a =~ b::s ↔ ff :=
begin
  apply not_equiv_false,
  by_contra c,
  cases c,
  contradiction,
end

/-
Lemma char_eps_suffix : ∀(a : ascii) s, a :: s =~ Char a ↔ s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.
-/

lemma char_eps_suffix (a : char) (s) : Char a =~ a::s ↔ s = [] :=
begin
  split,
    intro h,
    cases h,
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

lemma app_exists (s: str) (re₀ re₁)
  : App re₀ re₁ =~ s ↔
    ∃s₀ s₁, s = s₀ ++ s₁ ∧ re₀ =~ s₀ ∧ re₁ =~ s₁ :=
begin
  split,
    intro h,
    with_cases {cases h},
    case : s₁ s₂ h₁ h₂ {
      exact ⟨s₁, s₂, rfl, h₁, h₂⟩,
    },
  intro h,
  cases h with w₁ h,
  cases h with w₂ h,
  rw h.left,
  exact MApp h.right.left h.right.right,
end

/-
Lemma app_ne : ∀(a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) ↔
    ([ ] =~ re0 ∧ a :: s =~ re1) ∨
    ∃s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re0 ∧ s1 =~ re1.
Proof.
  (* FILL IN HERE *) Admitted.
-/

/- use the previous lemma -/
/- suggest even says so for ← -/

lemma app_ne (a : char) (s re₀ re₁)
  : App re₀ re₁ =~ a::s ↔
    re₀ =~ [] ∧ re₁ =~ a::s ∨
    ∃s₀ s₁, s = s₀ ++ s₁ ∧ re₀ =~ a::s₀ ∧ re₁ =~ s₁ :=
begin
  split,
    intro h,
    rw app_exists at h,
    cases h with w₀ h,
    cases h with w₁ h,
      cases w₀ with h₀ t₀,
      cases h with hl hr,
      simp at hl,
      rw ←hl at hr,
      exact or.inl hr,
    cases h with hl hr,
    injection hl with hll hlr,
    cases hr with hrl hrr,
    rw ←hll at hrl,
    exact or.inr ⟨t₀, w₁, hlr, hrl, hrr⟩,
  intro h,
  rw app_exists,
  cases h,
    cases h with hl hr,
    exact ⟨[], a::s, rfl, hl, hr⟩,
  cases h with w₀ h,
  cases h with w₁ h,
  cases h with hl hr,
  cases hr with hm hr,
  rw hl,
  /- for the heck of it. existsi works -/
  existsi [a::w₀, w₁],
  exact ⟨rfl, hm, hr⟩,
end

/- this might eventually work, but it was clearly the wrong path -/

-- lemma app_ne (a : char) (s re₀ re₁)
--   : App re₀ re₁ =~ a::s ↔
--     re₀ =~ [] ∧ re₁ =~ a::s ∨
--     ∃s₀ s₁, s = s₀ ++ s₁ ∧ re₀ =~ a::s₀ ∧ re₁ =~ s₁ :=
-- begin
--   split,
--     generalize heq : a::s = s',
--     intro h,
--     with_cases {cases h},
--     case : s₁ s₂ h₁ h₂ {
--       induction h₁ generalizing s re₁ s₂,
--       case MEmpty {
--         simp,
--         exact or.inl ⟨MEmpty, h₂⟩,
--       },
--       case MChar : h₁' {
--         injection heq with heq₁ heq₂,
--         generalize heq' : Char h₁' = ch₁,
--         generalize heq'' : list.append [h₁'] s₂ = lh₁,
--         rw [heq', heq''] at h,
--         with_cases {cases h},
--         case : s₁' s₂' h₁' h₂' {
--           simp at heq₂,
--           rw [←heq', ←heq''] at *,
--           rw [←heq₁, ←heq₂] at *,
--           rw [←heq₂] at h₂, /- why doesn't this get rewritten by *? -/
--           exact or.inr ⟨[], s, rfl, MChar a, h₂⟩,
--         },
--       },
--       case MApp : s₁' re₁' s₂' re₂' h₁' h₂' ih₁ ih₂ {

--         exact or.inr ⟨⟩,
--       },
--     }
-- end

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

lemma union_disj (s : str) (re₀ re₁)
  : Union re₀ re₁ =~ s ↔ re₀ =~ s ∨ re₁ =~ s :=
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

lemma star_ne (a : char) (s re)
  : Star re =~ a::s ↔
    ∃s₀ s₁, s = s₀ ++ s₁ ∧ re =~ a::s₀ ∧ Star re =~ s₁ :=
begin
  split,
    generalize heq : a::s = s',
    generalize heq' : Star re = re',
    intro h,
    induction h,
    all_goals { try { contradiction, } },
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
  intro h,
  cases h with w₀ h,
  cases h with w₁ h,
  rw h.left,
  rw ←cons_append,
  exact MStarApp h.right.left h.right.right,
end

/-
Definition refl_matches_eps m :=
  ∀re : @reg_exp ascii, reflect ([ ] =~ re) (m re).
-/

def refl_matches_eps (m : reg_exp char → bool) := ∀re, reflect' (re =~ []) (m re)

/-
Fixpoint match_eps (re: @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def match_eps : reg_exp char → bool
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

/- yeah, lean does not do well here -/

lemma match_eps_refl : refl_matches_eps match_eps :=
begin
  unfold refl_matches_eps,
  intro re,
  induction re,
  case EmptySet {
    constructor,
    by_contra c,
    cases c,
  },
  case EmptyStr {
    constructor,
    exact MEmpty,
  },
  case Char {
    constructor,
    by_contra c,
    cases c,
  },
  case App : re₁ re₂ ih₁ ih₂ {
    generalize heq₁ : (re₁ =~ []) = re₁',
    generalize hmeq₁ : match_eps re₁ = m₁',
    rw [heq₁, hmeq₁] at ih₁,
    generalize heq₂ : (re₂ =~ []) = re₂',
    generalize hmeq₂ : match_eps re₂ = m₂',
    rw [heq₂, hmeq₂] at ih₂,
    unfold match_eps,
    cases ih₁,
    case ReflectT : ih₁' {
      rw ←heq₁ at ih₁',
      cases ih₂,
      case ReflectT : ih₂' {
        rw [hmeq₁, hmeq₂],
        simp,
        rw ←heq₂ at ih₂',
        exact ReflectT (MApp ih₁' ih₂'),
      },
      case ReflectF : ih₂' {
        rw [hmeq₁, hmeq₂],
        simp,
        rw ←heq₂ at ih₂',
        apply ReflectF,
        by_contra c,
        generalize hc : App re₁ re₂ = c',
        generalize hc' : (nil : str) = n,
        rw [hc, hc'] at c,
        cases c,
        all_goals { try { contradiction, } },
        case MApp : s₁ re₁'' s₂ re₂'' h₁ h₂ {
          injection hc with hcl hcr,
          rw ←hcr at h₂,
          have : s₂ = nil,
            cases s₁,
              symmetry,
              exact hc',
            contradiction,
          rw this at h₂,
          contradiction,
        },
      },
    },
    case ReflectF : ih₁' {
      rw ←heq₁ at ih₁',
      rw [hmeq₁, hmeq₂],
      simp,
      apply ReflectF,
      by_contra c,
      generalize hc : App re₁ re₂ = c',
      generalize hc' : (nil : str) = n,
      rw [hc, hc'] at c,
      cases c,
      all_goals { try { contradiction, } },
      case MApp : s₁ re₁'' s₂ re₂'' h₁ h₂ {
        injection hc with hcl hcr,
        rw ←hcl at h₁,
        have : s₁ = nil,
          cases s₁,
            refl,
          contradiction,
        rw this at h₁,
        contradiction,
      },
    },
  },
  case Union : re₁ re₂ ih₁ ih₂ {
    generalize heq₁ : (re₁ =~ []) = re₁',
    generalize hmeq₁ : match_eps re₁ = m₁',
    rw [heq₁, hmeq₁] at ih₁,
    generalize heq₂ : (re₂ =~ []) = re₂',
    generalize hmeq₂ : match_eps re₂ = m₂',
    rw [heq₂, hmeq₂] at ih₂,
    unfold match_eps,
    cases ih₁,
    case ReflectT : ih₁' {
      rw [hmeq₁, hmeq₂],
      simp,
      rw ←heq₁ at ih₁',
      exact ReflectT (MUnionL re₂ ih₁'),
    },
    case ReflectF : ih₁' {
      rw ←heq₁ at ih₁',
      cases ih₂,
      case ReflectT : ih₂' {
        rw [hmeq₁, hmeq₂],
        simp,
        rw ←heq₂ at ih₂',
        exact ReflectT (MUnionR re₁ ih₂'),
      },
      case ReflectF : ih₂' {
        rw [hmeq₁, hmeq₂],
        simp,
        rw ←heq₂ at ih₂',
        apply ReflectF,
        by_contra c,
        generalize hc : Union re₁ re₂ = c',
        generalize hc' : (nil : str) = n,
        rw [hc, hc'] at c,
        cases c,
        all_goals { try { contradiction, } },
        case MUnionL : _ re₁'' re₂'' h {
          injection hc with hcl hcr,
          rw [←hcl, ←hc'] at h,
          contradiction,
        },
        case MUnionR : _ re₁'' re₂'' h {
          injection hc with hcl hcr,
          rw [←hcr, ←hc'] at h,
          contradiction,
        }
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

def is_der (re) (a : char) (re') :=
  ∀s, re =~ a::s ↔ re' =~ s

/-
Definition derives d := ∀a re, is_der re a (d a re).
-/

def derives (d : char → reg_exp char → reg_exp char) :=
  ∀a re, is_der re a (d a re)

/-
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def derive (a : char) : reg_exp char → reg_exp char
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

example : match_eps (derive d (derive c (App (Char c) (Char d)))) = tt :=
  by simp [derive, match_eps]

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

lemma derive_corr : derives derive :=
begin
  unfold derives,
  unfold is_der,
  intros,
  split,
    intro h,
    induction re generalizing s,
    case EmptySet { cases h, },
    case EmptyStr { cases h, },
    case Char {
      cases h,
      unfold derive,
      simp,
      exact MEmpty,
    },
    case App : re₁ re₂ ih₁ ih₂ {
      unfold derive,
      rw app_ne at h,
      have, exact match_eps_refl re₁,
      generalize heq : (re₁ =~ []) = re₁',
      rw heq at this,
      generalize heq' : match_eps re₁ = me',
      rw heq' at this,
      cases h,
        /-
        TODO - try using reflect in earlier exercises like this
        -/
        cases this,
        case ReflectT : this {
          simp,
          exact MUnionR _ (ih₂ s h.right),
        },
        case ReflectF : this {
          rw ←heq at this,
          cases this with hl hr,
          exact absurd h.left hr,
        },
      cases this,
      case ReflectT : this {
        simp,
        cases h with s₀ h,
        cases h with s₁ h,
        apply MUnionL,
        rw app_exists _ _ _,
        exact ⟨s₀, s₁, h.left, ih₁ _ h.right.left, h.right.right⟩,
      },
      case ReflectF : this {
        simp,
        cases h with s₀ h,
        cases h with s₁ h,
        rw app_exists _ _ _,
        exact ⟨s₀, s₁, h.left, ih₁ _ h.right.left, h.right.right⟩,
      },
    },
    case Union : re₁ re₂ ih₁ ih₂ {
      unfold derive,
      rw union_disj at h,
      cases h,
        exact MUnionL _ (ih₁ _ h),
      exact MUnionR _ (ih₂ _ h),
    },
    case Star : re ih {
      unfold derive,
      rw star_ne at h,
      cases h with s₀ h,
      cases h with s₁ h,
      rw app_exists,
      exact ⟨s₀, s₁, h.left, ih _ h.right.left, h.right.right⟩,
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
    constructor,
  },
  case App : re₁ re₂ ih₁ ih₂ {
    unfold derive at h,
    rw app_ne,
    cases hm : match_eps re₁,
      simp * at h,
      rw app_exists at h,
      cases h with s₀ h,
      cases h with s₁ h,
      exact or.inr ⟨_, _, h.left, ih₁ _ h.right.left, h.right.right⟩,
    simp * at h,
    rw union_disj at h,
    cases h,
      rw app_exists at h,
      cases h with s₀ h,
      cases h with s₁ h,
      exact or.inr ⟨_, _, h.left, ih₁ _ h.right.left, h.right.right⟩,
    have, exact match_eps_refl re₁,
    rw hm at this,
    cases this with this,
    exact or.inl ⟨this, ih₂ _ h⟩,
  },
  case Union : re₁ re₂ ih₁ ih₂ {
    unfold derive at h,
    rw union_disj at h,
    rw union_disj,
    cases h,
      exact or.inl (ih₁ _ h),
    exact or.inr (ih₂ _ h),
  },
  case Star : re ih {
    unfold derive at h,
    rw app_exists at h,
    cases h with s₀ h,
    cases h with s₁ h,
    rw star_ne,
    exact ⟨_, _, h.left, ih _ h.right.left, h.right.right⟩,
  },
end

/-
Definition matches_regex m : Prop :=
  ∀(s : string) re, reflect (s =~ re) (m s re).
-/

def matches_regex (m : str → reg_exp char → bool) :=
  ∀s re, reflect' (re =~ s) (m s re)

/-
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def regex_match : str → reg_exp char → bool
| [] r := match_eps r
| (c::s) r := regex_match s (derive c r)

/-
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem regex_refl : matches_regex regex_match :=
begin
  unfold matches_regex,
  intros,
  induction s generalizing re,
  case nil { exact match_eps_refl re, },
  case cons : hd tl ih {
    rw derive_corr,
    unfold regex_match,
    exact ih (derive hd re),
  },
end