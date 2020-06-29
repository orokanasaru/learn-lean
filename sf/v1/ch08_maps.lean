import tactic.basic
import .ch07_indprop

open indprop (reflect)
open indprop.reflect

variables {α : Type}
variables {a : α}
variables {s x y : string}

namespace maps

/-
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
-/

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
    cases c rfl,
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

/-
TODO: sf never explains subst
-/

theorem eqb_string_tt_iff : eqb_string x y = tt ↔ x = y :=
begin
  unfold eqb_string,
  cases string.has_decidable_eq x y,
    unfold ite,
    simp only [false_iff],
    exact h,
  subst h,
  unfold ite,
  simp only [true_iff, eq_self_iff_true],
end

/-
Theorem eqb_string_false_iff : ∀x y : string,
    eqb_string x y = false ↔ x ≠ y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.
-/

theorem eqb_string_ff_iff : eqb_string x y = ff ↔ x ≠ y :=
begin
  rw ne.def,
  rw ←eqb_string_tt_iff,
  rw eq_ff_eq_not_eq_tt,
end

/-
Theorem false_eqb_string : ∀x y : string,
   x ≠ y → eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.
-/

theorem ff_eqb_string (x y : string) (h : x ≠ y)
  : eqb_string x y = ff := eqb_string_ff_iff.mpr h

/-
Definition total_map (A : Type) := string → A.
-/

def total_map (α : Type) := string → α

/-
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ ⇒ v).
-/

def t_empty (v) : total_map α := λ_, v

/-
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' ⇒ if eqb_string x x' then v else m x'.
-/

def t_update (m : total_map α) (x) (v : α) :=
  λx', if eqb_string x x' then v else m x'

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

lemma t_apply_empty (x) (v : α) : (__ !→ v) x = v := rfl

/-
Lemma t_update_eq : ∀(A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma t_update_eq (m x) (v : α) : (x !→ v ; m) x = v :=
begin
  unfold t_update,
  unfold eqb_string,
  simp only [if_true, bool.coe_sort_tt, eq_self_iff_true],
end

/-
Theorem t_update_neq : ∀(A : Type) (m : total_map A) x1 x2 v,
    x1 ≠ x2 →
    (x1 !-> v ; m) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem t_update_neq (m x₁ x₂) (v : α) (h : x₁ ≠ x₂)
  : (x₁ !→ v ; m) x₂ = m x₂ :=
begin
  unfold t_update,
  unfold eqb_string,
  simp only [h, bool.coe_sort_ff, if_false],
end

/-
Lemma t_update_shadow : ∀(A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma t_update_shadow (m x) (v₁ v₂ : α)
  : (x !→ v₂ ; x !→ v₁ ; m) = (x !→ v₂ ; m) :=
begin
  unfold t_update,
  unfold eqb_string,
  funext,
  cases string.has_decidable_eq x x',
    simp only [h, bool.coe_sort_ff, if_false],
  simp only [h, if_true, bool.coe_sort_tt, eq_self_iff_true],
end

lemma eqb_stringP (x y : string) : reflect (x = y) (eqb_string x y) :=
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

theorem t_update_same (m : total_map α) (x) : (x !→ m x ; m) = m :=
begin
  unfold t_update,
  funext,
  have hr, exact eqb_stringP x x',
  revert hr,
  generalize heq : x = x' = h,
  generalize heq' : eqb_string x x' = he,
  intro,
  cases hr with hr' hr',
    subst_vars,
    refl,
  refl,
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

theorem t_update_permute (m) (v₁ v₂ : α) (x₁ x₂) (h : x₂ ≠ x₁)
  : (x₁ !→ v₁ ; (x₂ !→ v₂ ; m)) = (x₂ !→ v₂ ; (x₁ !→ v₁ ; m)) :=
begin
  unfold t_update,
  funext,
  have eqb₁, exact eqb_stringP x₁ x',
  have eqb₂, exact eqb_stringP x₂ x',
  revert_after x',
  generalize heq₁ : x₁ = x' = h₁,
  generalize heq₁' : eqb_string x₁ x' = h₁',
  generalize heq₂ : x₂ = x' = h₂,
  generalize heq₂' : eqb_string x₂ x' = h₂',
  intros,
  cases eqb₁ with eqb₁' eqb₁',
    cases eqb₂ with eqb₂' eqb₂',
      subst_vars,
      cases h rfl,
    refl,
  refl,
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

def empty : partial_map α := t_empty none

def update (m x) (v : α) := (x !→ some v ; m)

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

notation x ` |→ `:10 v := update empty x v

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

lemma apply_empty (α x) : @empty α x = none :=
begin
  unfold empty,
  rw t_apply_empty,
end

lemma update_eq (m x) (v : α) : (x |→ v ; m) x = some v :=
begin
  unfold update,
  rw t_update_eq,
end

theorem update_neq (m x₁ x₂) (v : α) (h : x₂ ≠ x₁)
  : (x₂ |→ v ; m) x₁ = m x₁ :=
begin
  unfold update,
  rwa t_update_neq,
end

theorem update_shadow (m x) (v₁ v₂ : α)
  : (x |→ v₂ ; x |→ v₁ ; m) = (x |→ v₂ ; m) :=
begin
  unfold update,
  rw t_update_shadow,
end

theorem update_same (m : partial_map α) (x v) (h : m x = some v)
  : (x |→ v ; m) = m :=
begin
  unfold update,
  rw ←h,
  rw t_update_same,
end

theorem update_permute (m x₁ x₂) (v₁ v₂ : α) (h : x₂ ≠ x₁)
  : (x₁ |→ v₁ ; x₂ |→ v₂ ; m) = (x₂ |→ v₂ ; x₁ |→ v₁ ; m) :=
begin
  unfold update,
  rwa t_update_permute,
end

end maps