import tactic.basic
import tactic.omega
import .ch11_imp

open imp

/-
Open Scope imp_scope.
Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O ⇒ empty_st
  | S i' ⇒
    match c with
      | SKIP ⇒
          st
      | l ::= a1 ⇒
          (l !-> aeval st a1 ; st)
      | c1 ;; c2 ⇒
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | TEST b THEN c1 ELSE c2 FI ⇒
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END ⇒
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.
Close Scope imp_scope.
-/

open nat

def ceval_step₂ : imp.state → com → ℕ → imp.state
| st c 0 := empty_st
| st SKIP (succ i) := st
| st (l ::= a₁) (succ i) := l !→ aeval st a₁ ; st
| st (c₁ ;; c₂) (succ i) :=
  let st' := ceval_step₂ st c₁ i in
  ceval_step₂ st' c₂ i
| st (TEST b THEN c₁ ELSE c₂ FI) (succ i) :=
  if beval st b
  then ceval_step₂ st c₁ i
  else ceval_step₂ st c₂ i
| st (WHILE b DO c END) (succ i) :=
  if beval st b
  then
    let st' := ceval_step₂ st c i in
    ceval_step₂ st' c i
  else st

/-
Open Scope imp_scope.
Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O ⇒ None
  | S i' ⇒
    match c with
      | SKIP ⇒
          Some st
      | l ::= a1 ⇒
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 ⇒
          match (ceval_step3 st c1 i') with
          | Some st' ⇒ ceval_step3 st' c2 i'
          | None ⇒ None
          end
      | TEST b THEN c1 ELSE c2 FI ⇒
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END ⇒
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' ⇒ ceval_step3 st' c i'
               | None ⇒ None
               end
          else Some st
    end
  end.
Close Scope imp_scope.
-/

def ceval_step₃ : imp.state → com → ℕ → option imp.state
| st c 0 := none
| st SKIP (succ i) := some st
| st (l ::= a₁) (succ i) := some $ l !→ aeval st a₁ ; st
| st (c₁ ;; c₂) (succ i) :=
  match ceval_step₃ st c₁ i with
  | some st' := ceval_step₃ st' c₂ i
  | none := none
  end
| st (TEST b THEN c₁ ELSE c₂ FI) (succ i) :=
  if beval st b
  then ceval_step₃ st c₁ i
  else ceval_step₃ st c₂ i
| st (WHILE b DO c END) (succ i) :=
  if beval st b
  then
    match ceval_step₃ st c i with
    | some st' := ceval_step₃ st' c i
    | none := none
    end
  else st

/-
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x ⇒ e2
         | None ⇒ None
       end)
   (right associativity, at level 60).
Open Scope imp_scope.
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O ⇒ None
  | S i' ⇒
    match c with
      | SKIP ⇒
          Some st
      | l ::= a1 ⇒
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 ⇒
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | TEST b THEN c1 ELSE c2 FI ⇒
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END ⇒
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None ⇒ None
  | Some st ⇒ Some (st X, st Y, st Z)
  end.

(* Compute
     (test_ceval empty_st
         (X ::= 2;;
          TEST (X <= 1)
            THEN Y ::= 3
            ELSE Z ::= 4
          FI)).
   ====>
      Some (2, 0, 4)   *)
-/

/- nah, not doing the notation -/
/- but the match is better -/

def ceval_step : imp.state → com → ℕ → option imp.state
| st c 0 := none
| st c (succ i) :=
  match c with
  | SKIP := some st
  | l ::= a₁ := some $ l !→ aeval st a₁ ; st
  | c₁ ;; c₂ := do st' ← ceval_step st c₁ i, ceval_step st' c₂ i
  | TEST b THEN c₁ ELSE c₂ FI :=
    if beval st b
    then ceval_step st c₁ i
    else ceval_step st c₂ i
  | WHILE b DO c₁ END :=
    if beval st b
    then do st' ← ceval_step st c₁ i, ceval_step st' c i
    else st
  end

def test_ceval (st c) :=
  do st ← ceval_step st c 500, pure (st X, st Y, st Z)

#eval test_ceval empty_st $
  X ::= 2;;
  TEST X ≤' 1
    THEN Y ::= 3
    ELSE Z ::= 4
  FI

/-
Definition pup_to_n : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(*

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
*)
-/

def pup_to_n' : com :=
  Y ::= 0;;
  WHILE ¬X == 0 DO
    Y ::= Y + X;;
    X ::= X - 1
  END

example : test_ceval (X !→ 5) pup_to_n' = some (0, 15, 0) := rfl

def is_even : com :=
  WHILE 2 ≤' X DO X ::= X - 2 END;;
  TEST X == 0 THEN Z ::= 0 ELSE Z ::= 1 FI

example : test_ceval (X !→ 5) is_even = some (1, 0, 1) := rfl

example : test_ceval (X !→ 10) is_even = some (0, 0, 0) := rfl

/-
Theorem ceval_step__ceval: ∀c st st',
      (∃i, ceval_step st c i = Some st') →
      st =[ c ]⇒ st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.
  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* SKIP *) apply E_Skip.
      + (* ::= *) apply E_Ass. reflexivity.
      + (* ;; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.
      + (* TEST *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
      + (* WHILE *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H1. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1. intros H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.
-/

open imp.com imp.ceval

theorem ceval_step__ceval {c st st'} (h : ∃i, ceval_step st c i = some st')
  : st =[ c ]⇒ st' :=
begin
  cases h with i h,
  induction i with i ih generalizing c st st',
    cases h,
  cases c; simp [ceval_step] at h,
  case CSkip {
    subst h,
    exact E_Skip st,
  },
  case CAss : x a {
    subst h,
    apply E_Ass,
    refl,
  },
  case CSeq : c₁ c₂ {
    cases h with a h,
    exact E_Seq (ih h.left) (ih h.right),
  },
  case CIf : b c₁ c₂ {
    cases heq: beval st b; rw heq at h; simp at h,
      exact E_IfFalse c₁ heq (ih h),
    exact E_IfTrue c₂ heq (ih h),
  },
  case CWhile : b c {
    cases heq: beval st b; rw heq at h; simp at h,
      cases h,
      exact E_WhileFalse c heq,
    cases h with a h,
    exact E_WhileTrue heq (ih h.left) (ih h.right),
  },
end

/-
Theorem ceval_step_more: ∀i1 i2 st st' c,
  i1 ≤ i2 →
  ceval_step st c i1 = Some st' →
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' ≤ i2') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.
    + (* TEST *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
    + (* WHILE *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite → Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval. Qed.
-/

theorem ceval_step_more {i₁ i₂ st st' c}
  (hl : i₁ ≤ i₂) (h: ceval_step st c i₁ = some st')
  : ceval_step st c i₂ = some st' :=
begin
  induction i₁ with i₁ ih generalizing i₂ st st' c,
    unfold ceval_step at h,
    cases h,
  cases i₂,
    cases hl,
  /- omega failed here (yikes) -/
  have hl, exact le_of_succ_le_succ hl,
  cases c,
  case CSkip {
    cases h,
    unfold ceval_step,
  },
  case CAss : x a {
    unfold ceval_step at *,
    assumption,
  },
  case CSeq : c₁ c₂ {
    unfold ceval_step at *,
    cases h₁ : ceval_step st c₁ i₁ with st'',
      simp only [ceval_step, h₁] at h,
      contradiction,
    simp only [h₁, option.some_bind] at h,
    simp only [ih hl h₁, ih hl h, option.some_bind],
  },
  case CIf : b c₁ c₂ {
    unfold ceval_step at *,
    cases beval st b; simp at *; exact ih hl h,
  },
  case CWhile : b c {
    unfold ceval_step at *,
    cases beval st b; simp at *,
      exact h,
    cases h with a h,
    exact ⟨a, ih hl h.left, ih hl h.right⟩,
  },
end

/-
Theorem ceval__ceval_step: ∀c st st',
      st =[ c ]⇒ st' →
      ∃i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  (* FILL IN HERE *) Admitted.
-/

lemma le_max (n m : ℕ) : n ≤ max n m ∧ m ≤ max n m :=
begin
  simp only [le_max_iff],
  split,
    exact or.inl (refl _),
  exact or.inr (refl _),
end

theorem ceval__ceval_step {c st st'} (h : st =[ c ]⇒ st')
  : ∃i, ceval_step st c i = some st' :=
begin
  induction h,
  case E_Skip { exact ⟨1, rfl⟩, },
  case E_Ass : st a n x h {
    exact ⟨1, by simp only [ceval_step, h]⟩,
  },
  case E_Seq : c₁ c₂ st'' st''' st'''' h₁ h₂ ih₁ ih₂ {
    cases ih₁ with i₁ ih₁,
    cases ih₂ with i₂ ih₂,
    exact ⟨max i₁ i₂ + 1, by {
      unfold ceval_step,
      have hl, exact le_max i₁ i₂,
      simp [ceval_step_more hl.left ih₁, ceval_step_more hl.right ih₂],
    }⟩,
  },
  case E_IfTrue : st'' st''' b c₁ c₂ h₁ h₂ ih {
    cases ih with i ih,
    exact ⟨i + 1, by {
      unfold ceval_step,
      simp [h₁, ih],
    }⟩,
  },
  case E_IfFalse : st'' st''' b c₁ c₂ h₁ h₂ ih {
    cases ih with i ih,
    exact ⟨i + 1, by {
      unfold ceval_step,
      simp [h₁, ih],
    }⟩,
  },
  case E_WhileFalse : b st'' c h {
    exact ⟨1, by {
      unfold ceval_step,
      simp [h],
      refl,
    }⟩,
  },
  case E_WhileTrue : st'' st''' st'''' b c hb h₂ h₃ ih₁ ih₂ {
    cases ih₁ with i₁ ih₁,
    cases ih₂ with i₂ ih₂,
    exact ⟨max i₁ i₂ + 1, by {
      unfold ceval_step,
      simp [hb],
      exact ⟨st''', by {
        have hl, exact le_max i₁ i₂,
        exact ⟨ceval_step_more hl.left ih₁, ceval_step_more hl.right ih₂⟩,
      }⟩,
    }⟩,
  },
end

/-
Theorem ceval_and_ceval_step_coincide: ∀c st st',
      st =[ c ]⇒ st'
  ↔ ∃i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.
-/

theorem ceval_and_ceval_step_coincide (c st st')
  : (st =[ c ]⇒ st') ↔ ∃i, ceval_step st c i = some st' :=
⟨ceval__ceval_step, ceval_step__ceval⟩

/-
Theorem ceval_deterministic' : ∀c st st1 st2,
     st =[ c ]⇒ st1 →
     st =[ c ]⇒ st2 →
     st1 = st2.

Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega. Qed.
-/

theorem ceval_deterministic' {c st st₁ st₂}
  (h₁ : st =[ c ]⇒ st₁) (h₂ : st =[ c ]⇒ st₂) : st₁ = st₂ :=
begin
  cases ceval__ceval_step h₁ with i₁ h₁,
  cases ceval__ceval_step h₂ with i₂ h₂,
  replace h₂, exact ceval_step_more (le_max i₁ i₂).right h₂,
  rw ceval_step_more (le_max i₁ i₂).left h₁ at h₂,
  injection h₂,
end