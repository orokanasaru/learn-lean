import data.nat.basic
import .ch01_basics

namespace lists

/-
  nb. i skipped from induction to tactics
  the bits using lists and polymorphism there annoyed me
  whoops

  let's see how well i can ignore those tactics in the
  next two chapters that should precede them
-/

/-
Inductive natprod : Type :=
| pair (n1 n2 : nat).
-/

inductive natprod : Type
| pair (n1 n2 : ℕ)

open natprod

/-
Check (pair 3 5).
-/

#check pair 3 5

/-
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y ⇒ x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y ⇒ y
  end.
Compute (fst (pair 3 5)).
(* ===> 3 *)
-/

definition fst (p : natprod) : ℕ :=
match p with
| (pair x _) := x
end

definition snd : natprod → ℕ
| (pair _ y) := y

#reduce fst (pair 3 5)

/-
Notation "( x , y )" := (pair x y).
-/

/-
using parentheses breaks things in surprising ways
definition of minus below fails to compile at first closing paren

update : using braces breaks typeclass instance definitions
-/
notation `⦃` x , y `⦄` := pair x y

/-
Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) ⇒ x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) ⇒ y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) ⇒ (y,x)
  end.
-/

#reduce fst ⦃ 3, 5 ⦄

def fst' : natprod → ℕ
| ⦃ x,_ ⦄ := x

def snd' : natprod → ℕ
| ⦃ _,y ⦄ := y

def swap_pair : natprod → natprod
| ⦃ x,y ⦄ := ⦃ y,x ⦄

/-
Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O   , _    ⇒ O
  | S _ , O    ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.
-/

/-
stated before, but lean doesn't allow recursion
with the match notation.
the point is to show comma fun, so i think it's ok
to use the built in subtraction
-/
def minus (n m : ℕ) : ℕ :=
match n, m with
| 0, _ := 0
| _, 0 := 0
| n + 1, m + 1 := n - m
end

/-
(* Can't match on a pair with multiple patterns: *)
Definition bad_fst (p : natprod) : nat :=
  match p with
  | x, y ⇒ x
  end.

(* Can't match on multiple values with pair patterns: *)
Definition bad_minus (n m : nat) : nat :=
  match n, m with
  | (O   , _   ) ⇒ O
  | (S _ , O   ) ⇒ n
  | (S n', S m') ⇒ bad_minus n' m'
  end.
-/

/-
honestly not sure about the point of this exercise
-/
/-
def bad_fst (p : natprod) : ℕ :=
match p with
| x, y := x
end

def bad_minus (n m : ℕ) : ℕ :=
match n, m with
| {0, _} := 0
| {_, 0} := n
| {n + 1, m + 1} := n - m
end
-/

/-
Theorem surjective_pairing' : ∀(n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.
-/

theorem surjective_pairing' (n m : ℕ)
  : ⦃n, m⦄ = ⦃fst ⦃n, m⦄, snd ⦃n, m⦄⦄ := rfl

/-
theorem surjective_pairing_stuck (p : natprod)
  : p = {fst p, snd p} :=
begin
  simp [fst, snd],
  /- abort -/
end
-/

/-
Theorem surjective_pairing : ∀(p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.
-/

theorem surjective_pairing (p : natprod)
  : p = ⦃ fst p, snd p ⦄ :=
by cases p; reflexivity

/-
Theorem snd_fst_is_swap : ∀(p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem snd_fst_is_swap (p : natprod)
  : ⦃snd p, fst p⦄ = swap_pair p :=
by cases p; reflexivity

/-
Theorem fst_swap_is_snd : ∀(p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem fst_swap_is_snd (p : natprod)
  : fst (swap_pair p) = snd p :=
by cases p; reflexivity

/-
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
-/

inductive natlist : Type
| nil
| cons (n : ℕ) (l : natlist)

open natlist

/-
Definition mylist := cons 1 (cons 2 (cons 3 nil)).
-/

def mylist := cons 1 (cons 2 (cons 3 nil))

/-
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
-/

/-
same as above. there are conflicts with core using brackets
not sure how the foldr notation works
-/
infixr ` :: ` := cons
notation `⟦` l:(foldr `, ` (h t, cons h t) nil `⟧`) := l

/-
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].
-/

def mylist1 := 1 :: (2 :: (3 :: nil))
def mylist2 := 1 :: 2 :: 3 :: nil
def mylist3 := ⟦1,2,3⟧

/-
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O ⇒ nil
  | S count' ⇒ n :: (repeat n count')
  end.
-/

def repeat (n : ℕ) : ℕ → natlist
| 0 := nil
| (m + 1) := n :: repeat m

/-
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil ⇒ O
  | h :: t ⇒ S (length t)
  end.
-/

@[simp]
def length : natlist → ℕ
| nil := 0
| (_ :: t) := length t + 1

/-
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil ⇒ l2
  | h :: t ⇒ h :: (app t l2)
  end.
-/

@[simp]
def app : natlist → natlist → natlist
| nil l2 := l2
| (h::t) l2 := h :: app t l2

/-
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.
-/

infix ` ++ ` := app

example : ⟦1,2,3⟧ ++ ⟦4,5⟧ = ⟦1,2,3,4,5⟧ := rfl
example : nil ++ ⟦4,5⟧ = ⟦4,5⟧ := rfl
example : ⟦1,2,3⟧ ++ nil = ⟦1,2,3⟧ := rfl

/-
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil ⇒ default
  | h :: t ⇒ h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.
-/

@[simp]
def hd (default : ℕ) : natlist → ℕ
| nil := default
| (h::_) := h

@[simp]
def tl : natlist → natlist
| nil := nil
| (_::t) := t

example : hd 0 ⟦1,2,3⟧ = 1 := rfl
example : hd 0 ⟦⟧ = 0 := rfl
example : tl ⟦1,2,3⟧ = ⟦2,3⟧ := rfl

/-
Fixpoint nonzeros (l:natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* FILL IN HERE *) Admitted.

Definition countoddmembers (l:natlist) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
def nonzeros : natlist → natlist
| ((n + 1)::t) := (n + 1)::nonzeros t
| (_::t) := nonzeros t
| _ := nil

example : nonzeros ⟦0,1,0,2,3,0,0⟧ = ⟦1,2,3⟧ := rfl

@[simp]
def filter (p : ℕ → bool) : natlist → natlist
| (h::t) := if p h then h::filter t else filter t
| _ := nil

def oddmembers := filter oddb

example : oddmembers ⟦0,1,0,2,3,0,0⟧ = ⟦1,3⟧ := rfl

def countoddmembers := length ∘ oddmembers

example : countoddmembers ⟦1,0,3,1,4,5⟧ = 4 := rfl

example : countoddmembers ⟦0,2,4⟧ = 0 := rfl

example : countoddmembers nil = 0 := rfl

/-
Fixpoint alternate (l1 l2 : natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* FILL IN HERE *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* FILL IN HERE *) Admitted.
-/

/- this is trivial in lean -/
def alternate : natlist → natlist → natlist
| nil r := r
| l nil := l
| (lh::lt) (rh::rt) := lh::rh::alternate lt rt

example : alternate ⟦1,2,3⟧ ⟦4,5,6⟧ = ⟦1,4,2,5,3,6⟧ := rfl

example : alternate ⟦1⟧ ⟦4,5,6⟧ = ⟦1,4,5,6⟧ := rfl

example : alternate ⟦1,2,3⟧ ⟦4⟧ = ⟦1,4,2,3⟧ := rfl

example : alternate ⟦⟧ ⟦20,30⟧ = ⟦20,30⟧ := rfl

/-
Definition bag := natlist.
-/

def bag := natlist

/-
Fixpoint count (v:nat) (s:bag) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

/- i really feel like i'm starting to miss the point -/
@[simp]
def count (v : ℕ) : bag → ℕ :=
  length ∘ filter (eqb v)

/-
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.
-/

example : count 1 ⟦1,2,3,1,4,1⟧ = 3 := rfl

example : count 6 ⟦1,2,3,1,4,1⟧ = 0 := rfl

/-
Definition sum : bag → bag → bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_member1: member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.

Example test_member2: member 2 [1;4;1] = false.
(* FILL IN HERE *) Admitted.
-/

/- sum is a reserved name for sum types -/
def bag.sum := app

example : count 1 (bag.sum ⟦1,2,3⟧ ⟦1,4,1⟧) = 3 := rfl

def add := cons

example : count 1 (add 1 ⟦1,4,1⟧) = 3 := rfl

example : count 5 (add 1 ⟦1,4,1⟧) = 0 := rfl

def member (v : ℕ) : bag → bool
| (h::t) := if eqb v h then tt else member t
| _ := ff

example : member 1 ⟦1,4,1⟧ = tt := rfl

example : member 2 ⟦1,4,1⟧ = ff := rfl

/-
Fixpoint remove_one (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* FILL IN HERE *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
-/

@[simp]
def remove_one (v : ℕ) : bag → bag
| (h::t) := if eqb v h then t else h::remove_one t
| _ := nil

example : count 5 (remove_one 5 ⟦2,1,5,4,1⟧) = 0 := rfl

example : count 5 (remove_one 5 ⟦2,1,4,1⟧) = 0 := rfl

example : count 4 (remove_one 5 ⟦2,1,4,5,1,4⟧) = 2 := rfl

example : count 5 (remove_one 5 ⟦2,1,5,4,5,1,4⟧) = 1 := rfl

def remove_all (v : ℕ) : bag → bag
| (h::t) := if eqb v h then remove_all t else h::remove_all t
| _ := nil

example : count 5 (remove_all 5 ⟦2,1,5,4,1⟧) = 0 := rfl

example : count 5 (remove_all 5 ⟦2,1,4,1⟧) = 0 := rfl

example : count 4 (remove_all 5 ⟦2,1,4,5,1,4⟧) = 2 := rfl

example : count 5 (remove_all 5 ⟦2,1,5,4,5,1,4,5,1,4⟧) = 0 := rfl

/- this is about the dumbest way i can think of -/
def subset : bag → bag → bool
| (h::t) b := if leb (count h (h::t)) (count h b)
              then subset t b
              else ff
| _ _ := tt

example : subset ⟦1,2⟧ ⟦2,1,4,1⟧ = tt := rfl

example : subset ⟦1,2,2⟧ ⟦2,1,4,1⟧ = ff := rfl

/-
Theorem nil_app : ∀l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.
-/

@[simp]
theorem nil_app (l : natlist) : ⟦⟧ ++ l = l := rfl

/-
Theorem tl_length_pred : ∀l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.
-/

/- TODO: be consistent about core vs defined usage -/
open nat

@[simp]
theorem tl_length_pred (l : natlist)
  : pred (length l) = length (tl l) :=
by cases l; refl

/-
Theorem app_assoc : ∀l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite → IHl1'. reflexivity. Qed.
-/

theorem app_assoc (l₁ l₂ l₃ : natlist)
  : (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) :=
begin
  induction l₁ with hd tl ih,
    refl,
  simp,
  rw ih
end

/-
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.
-/

@[simp]
def rev : natlist → natlist
| (h::t) := rev t ++ ⟦h⟧
| _ := ⟦⟧

example : rev ⟦1,2,3⟧ = ⟦3,2,1⟧ := rfl

example : rev nil = nil := rfl

/-
Theorem rev_length_firsttry : ∀l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l =  *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.
-/

/-
theorem rev_length_firsttry (l : natlist) :
  length (rev l) = length l :=
begin
  induction l with hd tl ih,
    refl,
  simp,
  rw ←ih,
  /- abort -/
end
-/

/-
Theorem app_length : ∀l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite → IHl1'. reflexivity. Qed.
-/

@[simp]
theorem app_length (l₁ l₂ : natlist)
  : length (l₁ ++ l₂) = (length l₁) + (length l₂) :=
begin
  induction l₁; simp [*, add_assoc, add_comm 1],
end

/-
Theorem rev_length : ∀l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite → app_length, plus_comm.
    simpl. rewrite → IHl'. reflexivity. Qed.
-/

@[simp]
theorem rev_length (l: natlist) : length (rev l) = length l :=
by induction l; simp *

/-
(*  Search rev. *)
-/

/-
  not great, but
  ctrl+p #
-/

/-
Theorem app_nil_r : ∀l : natlist,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_app_distr: ∀l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.

Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : ∀l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem app_nil_r (l : natlist) : l ++ ⟦⟧ = l :=
by induction l; simp *

@[simp]
theorem rev_app_distr (l₁ l₂ : natlist)
  : rev (l₁ ++ l₂) = rev l₂ ++ rev l₁ :=
by induction l₁; simp [*, ←app_assoc]

@[simp]
theorem rev_involutive (l : natlist)
  : rev (rev l) = l :=
by induction l; simp *

/-
Theorem app_assoc4 : ∀l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem app_assoc4 (l₁ l₂ l₃ l₄ : natlist)
  : l₁ ++ (l₂ ++ (l₃ ++ l₄)) = ((l₁ ++ l₂) ++ l₃) ++ l₄ :=
by simp [app_assoc]

lemma nonzeros_app (l₁ l₂ : natlist) :
  nonzeros (l₁ ++ l₂) = (nonzeros l₁) ++ (nonzeros l₂) :=
begin
  induction l₁ with h,
    refl,
  cases h; simp *,
end

/-
Fixpoint eqblist (l1 l2 : natlist) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_eqblist1 :
  (eqblist nil nil = true).
 (* FILL IN HERE *) Admitted.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
(* FILL IN HERE *) Admitted.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem eqblist_refl : ∀l:natlist,
  true = eqblist l l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
def eqblist : natlist → natlist → bool
| nil nil := tt
| (h₁::t₁) (h₂::t₂) := if eqb h₁ h₂
                       then eqblist t₁ t₂
                       else ff
| _ _ := ff

example : eqblist nil nil := rfl

example : eqblist ⟦1,2,3⟧ ⟦1,2,3⟧ := rfl

example : eqblist ⟦1,2,3⟧ ⟦1,2,4⟧ = ff := rfl

@[simp]
lemma eqb_refl (l : ℕ) : eqb l l = tt :=
by induction l; simp *

/-- tt on left is real bad for simplifications -/
theorem eqblist_refl (l : natlist) : eqblist l l = tt :=
by induction l; simp [*, eqb_refl]

/-
Theorem count_member_nonzero : ∀(s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
lemma zero_leb (n : nat) : 0 <=? n :=
by induction n; simp *

theorem count_member_nonzero (s : bag)
  : 1 <=? (count 1 (1 :: s)) = tt :=
by induction s; apply zero_leb

/-
Theorem leb_n_Sn : ∀n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.
-/

@[simp]
theorem leb_n_Sn (n : ℕ) : n <=? succ n = tt :=
by induction n; simp *

/-
Theorem remove_does_not_increase_count: ∀(s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem remove_does_not_increase_count (s : bag)
  : count 0 (remove_one 0 s) <=? count 0 s = tt :=
begin
  induction s with h t ih,
    simp,
  cases h,
    simp,
  /- simp is really great until it isn't -/
  exact ih,
end

/-
∀(l1 l2 : natlist), rev l1 = rev l2 → l1 = l2.
-/

/-
i think this is bs at this point
-/

@[simp]
lemma eq_app_nil_false
  {h : ℕ} {t : natlist} (c : t ++ ⟦h⟧ = nil) : false :=
begin
  have : length (t ++ ⟦h⟧) = length (nil),
    exact congr_arg length c,
  simp at this,
  contradiction,
end

@[simp]
lemma eq_nil_app_false
  {h : ℕ} {t : natlist} (c : nil = t ++ ⟦h⟧) : false :=
eq_app_nil_false (eq.symm c)

theorem snoc_injective' {h₁ h₂ : ℕ} : ∀ t₁ t₂ : natlist,
  t₁ ++ ⟦h₁⟧ = t₂ ++ ⟦h₂⟧ → h₁ = h₂ ∧ t₁ = t₂
| nil nil := by intro; simp * at *
| (h₁'::t₁) nil := by simp
| nil (h₂'::t₂) := by simp
| (h₁'::t₁) (h₂'::t₂) :=
begin
  intro h,
  simp at *,
  have : h₁ = h₂ ∧ t₁ = t₂,
    exact snoc_injective' t₁ t₂ h.right,
  exact ⟨this.left, h.left, this.right⟩,
end

theorem rev_injective' :
  ∀ l₁ l₂ : natlist, rev l₁ = rev l₂ → l₁ = l₂
| nil nil := by intro; simp
| nil (h₂::t₂) := by simp
| (h₁::t₁) nil := by simp
| (h₁::t₁) (h₂::t₂) :=
begin
  simp,
  intro h,
  have : h₁ = h₂ ∧ rev t₁ = rev t₂,
    exact snoc_injective' (rev t₁) (rev t₂) h,
  exact ⟨this.left, rev_injective' t₁ t₂ this.right⟩,
end

theorem snoc_injective {h₁ h₂ : ℕ} : ∀ t₁ t₂ : natlist,
  t₁ ++ ⟦h₁⟧ = t₂ ++ ⟦h₂⟧ → h₁ = h₂ ∧ t₁ = t₂ :=
begin
  intro t₁,
  induction t₁ with h₁' t₁ ih,
    intros t₂ h,
    cases t₂ with h₂' t₂,
      simp * at *,
    simp at h,
    contradiction,
  intro t₂,
  cases t₂ with h₂' t₂,
    simp,
  intro h,
  simp at *,
  have : h₁ = h₂ ∧ t₁ = t₂,
    exact ih t₂ h.right,
  exact ⟨this.left, h.left, this.right⟩,
end

theorem rev_injective :
  ∀ l₁ l₂ : natlist, rev l₁ = rev l₂ → l₁ = l₂ :=
begin
  intro l₁,
  induction l₁ with h₁ t₁ ih,
    intros l₂ h,
    cases l₂ with h₂ t₂,
      simp,
    simp at h,
    contradiction,
  intro l₂,
  cases l₂ with h₂ t₂,
    simp,
  intro h,
  simp at *,
  have : h₁ = h₂ ∧ rev t₁ = rev t₂,
    exact snoc_injective (rev t₁) (rev t₂) h,
  exact ⟨this.left, ih t₂ this.right⟩,
end

/-
lol, this is the easy way
-/

theorem rev_injective''
  (l₁ l₂ : natlist) (h : rev l₁ = rev l₂) : l₁ = l₂ :=
begin
  rw ←rev_involutive l₁,
  rw ←rev_involutive l₂,
  rw h
end

theorem rev_injective'''
  (l₁ l₂ : natlist) (h : rev l₁ = rev l₂) : l₁ = l₂ :=
begin
  have : rev (rev l₁) = rev (rev l₂),
    exact congr_arg rev h,
  simp at this,
  exact this
end

/-
Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil ⇒ 42 (* arbitrary! *)
  | a :: l' ⇒ match n =? O with
               | true ⇒ a
               | false ⇒ nth_bad l' (pred n)
               end
  end.
-/

def nth_bad : natlist → ℕ → ℕ
| nil _ := 42
| (h::_) 0 := h
| (_::t) (n + 1) := nth_bad t n

/-
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
-/

/- we're going to have a bad time -/
inductive natoption : Type
| some (n : ℕ)
| none

open natoption

/-
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil ⇒ None
  | a :: l' ⇒ match n =? O with
               | true ⇒ Some a
               | false ⇒ nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.

Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
-/

@[simp]
def nth_error : natlist → ℕ → natoption
| nil _ := none
| (h::_) 0 := some h
| (_::t) (n + 1) := nth_error t n

example : nth_error ⟦4,5,6,7⟧ 0 = some 4 := rfl

example : nth_error ⟦4,5,6,7⟧ 3 = some 7 := rfl

example : nth_error ⟦4,5,6,7⟧ 9 = none := rfl

/-
Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil ⇒ None
  | a :: l' ⇒ if n =? O then Some a
               else nth_error' l' (pred n)
  end.
-/

/-
yeah, we've been using ite already...
-/
def nth_error' : natlist → ℕ → natoption
| nil := λ _, none
| (h::t) := λ n, if n =? 0 then some h
                 else nth_error' t (pred n)

/-
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' ⇒ n'
  | None ⇒ d
  end.
-/

@[simp]
def option_elim (d : ℕ) : natoption → ℕ
| (some n) := n
| _ := d

/-
Definition hd_error (l : natlist) : natoption
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.
-/

@[simp]
def hd_error : natlist → natoption
| nil := none
| (h::_) := some h

example : hd_error ⟦⟧ = none := rfl

example : hd_error ⟦1⟧ = some 1 := rfl

example : hd_error ⟦5,6⟧ = some 5 := rfl

/-
Theorem option_elim_hd : ∀(l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem option_elim_hd (l : natlist) (default : ℕ)
  : hd default l = option_elim default (hd_error l) :=
by cases l; simp

/-
Inductive id : Type :=
  | Id (n : nat).
-/

/- a different id is already in scope -/
inductive Id : Type
| id (n : ℕ)

open Id

/-
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 ⇒ n1 =? n2
  end.
-/

@[simp]
def eqb_id : Id → Id → bool
| (id n₁) (id n₂) := n₁ =? n₂

/-
Theorem eqb_id_refl : ∀x, true = eqb_id x x.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem eqb_id_refl (x : Id) : eqb_id x x = tt :=
by cases x; simp

/-
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
-/

inductive partial_map : Type
| empty
| record (i : Id) (v : ℕ) (m : partial_map)

open partial_map

/-
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
-/

@[simp]
def update (d : partial_map) (x : Id) (value : ℕ)
  : partial_map := record x value d

/-
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty ⇒ None
  | record y v d' ⇒ if eqb_id x y
                     then Some v
                     else find x d'
  end.
-/

@[simp]
def find (x : Id) : partial_map → natoption
| empty := none
| (record y v d) := if eqb_id x y
                    then some v
                    else find d

/-
Theorem update_eq :
  ∀(d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
-/

theorem update_eq (d : partial_map) (x : Id) (v : ℕ) :
  find x (update d x v) = some v := by simp

/-
Theorem update_neq :
  ∀(d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false → find x (update d y o) = find x d.
Proof.
 (* FILL IN HERE *) Admitted.
-/

theorem update_neq
  (d : partial_map) (x y : Id) (o : ℕ) (h : eqb_id x y = ff) :
  find x (update d y o) = find x d :=
by simp *

/-
Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).
-/

/- i guess you can write it. you just can't make any -/
inductive baz : Type
| Baz1 (x : baz)
| Baz2 (y : baz) (b : bool)

end lists
