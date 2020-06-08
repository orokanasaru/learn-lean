import tactic.basic
import .ch07_indprop

/-
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
-/

/- i think that's all just lean prelude stuff -/

/-
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
-/

def eqb_string (x y : string) : bool :=
  if x = y then tt else ff

/-
Theorem eqb_string_refl : ∀s : string, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.
-/

theorem eqb_string_refl (s : string) : tt = eqb_string s s :=
begin
  unfold eqb_string,
  /- need the name for cases but not ite -/
  cases string.has_decidable_eq s s with c h,
    contradiction,
  refl,
end

/-
Theorem eqb_string_true_iff : ∀x y : string,
    eqb_string x y = true ↔ x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.
-/

theorem eqb_string_true_iff (x y : string)
  : eqb_string x y = tt ↔ x = y :=
begin
  unfold eqb_string,
  cases string.has_decidable_eq x y,
    unfold ite,
    simp,
    exact h,
  unfold ite,
  rw h,
  simp,
end

/-
Theorem eqb_string_false_iff : ∀x y : string,
    eqb_string x y = false ↔ x ≠ y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.
-/

theorem eqb_string_false_iff (x y : string)
  : eqb_string x y = ff ↔ x ≠ y :=
begin
  rw ne.def,
  rw ←eqb_string_true_iff,
  rw eq_ff_eq_not_eq_tt,
end

/-
Theorem false_eqb_string : ∀x y : string,
   x ≠ y → eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.
-/

theorem false_eqb_string (x y : string) (h : x ≠ y)
  : eqb_string x y = ff := (eqb_string_false_iff x y).mpr h

/-
Definition total_map (A : Type) := string → A.
-/

def total_map (α : Type) := string → α

/-
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ ⇒ v).
-/

def t_empty {α} (v) : total_map α := λ _, v

/-
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' ⇒ if eqb_string x x' then v else m x'.
-/

def t_update {α} (m : total_map α) (x) (v : α) :=
  λ x', if eqb_string x x' then v else m x'

/-
Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.
-/

def examplemap :=
  t_update (t_update (t_empty ff) "foo" tt) "bar" tt

/-
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).
-/

/- single _ doesn't work -/
notation `__` ` !→ `:10 v := t_empty v

example := __ !→ ff

/-
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
-/

/- here's how to assign precedence to parts of notation -/
notation x ` !→ `:10 v:5 ` ; ` m := t_update m x v

/-
Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).
-/

example := "bar" !→ tt ; "foo" !→ tt ; __ !→ ff

/-
Lemma t_apply_empty : ∀(A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma t_apply_empty {α} (x) (v : α) : (__ !→ v) x = v := rfl

/-
Lemma t_update_eq : ∀(A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma t_update_eq {α} (m x) (v : α)
  : (x !→ v ; m) x = v :=
begin
  unfold t_update,
  unfold eqb_string,
  simp,
end

/-
Theorem t_update_neq : ∀(A : Type) (m : total_map A) x1 x2 v,
    x1 ≠ x2 →
    (x1 !-> v ; m) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem t_update_neq {α} (m x₁ x₂) (v : α) (h : x₁ ≠ x₂)
  : (x₁ !→ v ; m) x₂ = m x₂ :=
begin
  unfold t_update,
  unfold eqb_string,
  simp [h],
end

/-
Lemma t_update_shadow : ∀(A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma t_update_shadow {α} (m x) (v₁ v₂ : α)
  : (x !→ v₂ ; x !→ v₁ ; m) = (x !→ v₂ ; m) :=
begin
  unfold t_update,
  unfold eqb_string,
  funext,
  cases string.has_decidable_eq x x',
    simp [h],
  simp [h],
end

open reflect'

lemma eqb_stringP (x y : string)
  : reflect' (x = y) (eqb_string x y) :=
begin
  unfold eqb_string,
  cases string.has_decidable_eq x y,
    exact ReflectF h,
  exact ReflectT h,
end

/-
Theorem t_update_same : ∀(A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem t_update_same {α} (m : total_map α) (x)
  : (x !→ m x ; m) = m :=
begin
  unfold t_update,
  funext,
  have, exact eqb_stringP x x',
  generalize heq : x = x' = h,
  generalize heq' : eqb_string x x' = h',
  rw [heq, heq'] at this,
  cases this,
  case ReflectT : this {
    rw ←heq at this,
    cases this with this,
    subst this,
    refl,
  },
  case ReflectF : this { refl, },
end

/-
Theorem t_update_permute : ∀(A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 ≠ x1 →
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem t_update_permute {α} (m) (v₁ v₂ : α) (x₁ x₂) (h : x₂ ≠ x₁)
  : (x₁ !→ v₁ ; (x₂ !→ v₂ ; m)) = (x₂ !→ v₂ ; (x₁ !→ v₁ ; m)) :=
begin
  unfold t_update,
  funext,
  have eqb₁, exact eqb_stringP x₁ x',
  generalize heq₁ : x₁ = x' = h₁,
  generalize heq₁' : eqb_string x₁ x' = h₁',
  rw [heq₁, heq₁'] at eqb₁,
  have eqb₂, exact eqb_stringP x₂ x',
  generalize heq₂ : x₂ = x' = h₂,
  generalize heq₂' : eqb_string x₂ x' = h₂',
  rw [heq₂, heq₂'] at eqb₂,
  cases eqb₁,
  case ReflectT : eqb₁' {
    simp,
    cases eqb₂,
    case ReflectT : eqb₂' {
      rw ←heq₁ at eqb₁',
      rw ←heq₂ at eqb₂',
      rw ←eqb₁' at eqb₂',
      contradiction,
    },
    case ReflectF : eqb₂ { refl, },
  },
  case ReflectF : eqb₁ { refl, },
end

/-
Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).
-/

def partial_map (α) := total_map (option α)

def empty' {α} : partial_map α := t_empty none

def update {α} (m x) (v : α) := (x !→ some v ; m)

/-
Notation "x '⊢>' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
-/

notation x ` |→ `:10 v:5 ` ; ` m := update m x v

/-
Notation "x '⊢>' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" ⊢> true ; "Turing" ⊢> false).
-/

notation x ` |→ `:10 v := update empty' x v

/-
Lemma apply_empty : ∀(A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : ∀(A : Type) (m : partial_map A) x v,
    (x ⊢> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : ∀(A : Type) (m : partial_map A) x1 x2 v,
    x2 ≠ x1 →
    (x2 ⊢> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : ∀(A : Type) (m : partial_map A) x v1 v2,
    (x ⊢> v2 ; x ⊢> v1 ; m) = (x ⊢> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : ∀(A : Type) (m : partial_map A) x v,
    m x = Some v →
    (x ⊢> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : ∀(A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 ≠ x1 →
    (x1 ⊢> v1 ; x2 ⊢> v2 ; m) = (x2 ⊢> v2 ; x1 ⊢> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.
-/

lemma apply_empty (α x) : @empty' α x = none :=
begin
  unfold empty',
  rw t_apply_empty,
end

lemma update_eq {α} (m x) (v : α)
  : (x |→ v ; m) x = some v :=
begin
  unfold update,
  rw t_update_eq,
end

theorem update_neq {α} (m x₁ x₂) (v : α) (h : x₂ ≠ x₁)
  : (x₂ |→ v ; m) x₁ = m x₁ :=
begin
  unfold update,
  rw t_update_neq,
  exact h,
end

theorem update_shadow {α} (m x) (v₁ v₂ : α)
  : (x |→ v₂ ; x |→ v₁ ; m) = (x |→ v₂ ; m) :=
begin
  unfold update,
  rw t_update_shadow,
end

theorem update_same {α} (m : partial_map α) (x v) (h : m x = some v)
  : (x |→ v ; m) = m :=
begin
  unfold update,
  rw ←h,
  rw t_update_same,
end

theorem update_permute {α} (m x₁ x₂) (v₁ v₂ : α) (h : x₂ ≠ x₁)
  : (x₁ |→ v₁ ; x₂ |→ v₂ ; m) = (x₂ |→ v₂ ; x₁ |→ v₁ ; m) :=
begin
  unfold update,
  rw t_update_permute,
  exact h,
end