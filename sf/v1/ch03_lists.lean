import data.nat.basic
import tactic.basic
import .ch01_basics

open basics (oddb eqb leb)
open nat (pred zero succ)

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

/- in lean, prod is actually a structure -/
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

definition fst : natprod → ℕ
| (pair x _) := x

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
should be okay if local
-/
local notation {x, y} := pair x y

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

#reduce fst {3, 5}

def fst' : natprod → ℕ
| {x, _} := x

def snd' : natprod → ℕ
| {_, y} := y

def swap_pair : natprod → natprod
| {x, y} := {y, x}

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
def minus : ℕ → ℕ → ℕ
| 0 _ := 0
| _ 0 := 0
| (n + 1) (m + 1) := minus n m

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
def bad_fst : natprod → ℕ
| x y := x

def bad_minus : ℕ → ℕ → ℕ
| {0, _} := 0
| {_, 0} := n
| {n + 1, m + 1} := n - m
-/

/-
Theorem surjective_pairing' : ∀(n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.
-/

theorem surjective_pairing' (n m : ℕ)
  : {n, m} = {fst {n, m}, snd {n, m}} := rfl

/-
Theorem surjective_pairing_stuck : ∀(p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.
-/

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

theorem surjective_pairing (p : natprod) : p = {fst p, snd p} :=
begin
  cases p with n m,
  refl,
end

/-
Theorem snd_fst_is_swap : ∀(p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem snd_fst_is_swap (p : natprod) : {snd p, fst p} = swap_pair p :=
begin
  cases p with n m,
  refl,
end

/-
Theorem fst_swap_is_snd : ∀(p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem fst_swap_is_snd (p : natprod) : fst (swap_pair p) = snd p :=
begin
  cases p with n m,
  refl,
end

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
local infixr :: := cons
local notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

/-
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].
-/

def mylist1 := 1 :: (2 :: (3 :: nil))
def mylist2 := 1 :: 2 :: 3 :: nil
def mylist3 := [1, 2, 3]

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

def append : natlist → natlist → natlist
| nil l2 := l2
| (h::t) l2 := h :: append t l2

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

infix ++ := append

example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := rfl
example : nil ++ [4, 5] = [4, 5] := rfl
example : [1, 2, 3] ++ nil = [1, 2, 3] := rfl

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

def head (default : ℕ) : natlist → ℕ
| nil := default
| (h::_) := h

def tail : natlist → natlist
| nil := nil
| (_::t) := t

example : head 0 [1, 2, 3] = 1 := rfl
example : head 0 [] = 0 := rfl
example : tail [1, 2, 3] = [2, 3] := rfl

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

def nonzeros : natlist → natlist
| ((n + 1)::t) := (n + 1)::nonzeros t
| (_::t) := nonzeros t
| _ := nil

example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := rfl

def filter (p : ℕ → bool) : natlist → natlist
| (h::t) := if p h then h::filter t else filter t
| _ := nil

def oddmembers := filter oddb

example : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] := rfl

def countoddmembers := length ∘ oddmembers

example : countoddmembers [1, 0, 3, 1, 4, 5] = 4 := rfl

example : countoddmembers [0, 2, 4] = 0 := rfl

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

def alternate : natlist → natlist → natlist
| nil r := r
| l nil := l
| (lh::lt) (rh::rt) := lh::rh::alternate lt rt

example : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] := rfl

example : alternate [1] [4, 5, 6] = [1, 4, 5, 6] := rfl

example : alternate [1, 2, 3] [4] = [1, 4, 2, 3] := rfl

example : alternate [] [20, 30] = [20, 30] := rfl

/-
Definition bag := natlist.
-/

def bag := natlist

/-
Fixpoint count (v:nat) (s:bag) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

/- i really feel like i'm starting to miss the point -/
def count (v : ℕ) : bag → ℕ :=
  length ∘ filter (eqb v)

/-
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.
-/

example : count 1 [1, 2, 3, 1, 4, 1] = 3 := rfl

example : count 6 [1, 2, 3, 1, 4, 1] = 0 := rfl

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

def sum := append

example : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3 := rfl

def add := cons

example : count 1 (add 1 [1, 4, 1]) = 3 := rfl

example : count 5 (add 1 [1, 4, 1]) = 0 := rfl

def member (v : ℕ) : bag → bool
| (h::t) := if eqb v h then tt else member t
| _ := ff

example : member 1 [1, 4, 1] = tt := rfl

example : member 2 [1, 4, 1] = ff := rfl

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

def remove_one (v : ℕ) : bag → bag
| (h::t) := if eqb v h then t else h::remove_one t
| _ := nil

example : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0 := rfl

example : count 5 (remove_one 5 [2, 1, 4, 1]) = 0 := rfl

example : count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2 := rfl

example : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1 := rfl

def remove_all (v : ℕ) : bag → bag
| (h::t) := if eqb v h then remove_all t else h::remove_all t
| _ := nil

example : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0 := rfl

example : count 5 (remove_all 5 [2, 1, 4, 1]) = 0 := rfl

example : count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2 := rfl

example : count 5 (remove_all 5 [2, 1, 5, 4, 5, 1, 4, 5, 1, 4]) = 0 := rfl

/- this is about the dumbest way i can think of -/
def subset : bag → bag → bool
| (h::t) b := if leb (count h (h::t)) (count h b)
              then subset t b
              else ff
| _ _ := tt

example : subset [1, 2] [2, 1, 4, 1] = tt := rfl

example : subset [1, 2, 2] [2, 1, 4, 1] = ff := rfl

/-
Theorem nil_app : ∀l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.
-/

theorem nil_append (l : natlist) : [] ++ l = l := rfl

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

theorem length_tail (l : natlist)
  : length (tail l) = pred (length l) :=
begin
  cases l with n l,
    refl,
  refl,
end

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

theorem cons_append (n : ℕ) (l₁ l₂ : natlist)
  : (n::l₁) ++ l₂ = n::(l₁ ++ l₂) := rfl

theorem append_assoc (l₁ l₂ l₃ : natlist)
  : (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) :=
begin
  induction l₁ with n l ih,
    refl,
  rw [cons_append, cons_append, cons_append],
  rw ih,
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

def reverse : natlist → natlist
| (h::t) := reverse t ++ [h]
| _ := []

example : reverse [1, 2, 3] = [3, 2, 1] := rfl

example : reverse nil = nil := rfl

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
theorem length_reverse_firsttry (l : natlist) :
  length (reverse l) = length l :=
begin
  induction l with n l ih,
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

theorem length_nil : length nil = 0 := rfl

theorem length_cons (n : ℕ) (l : natlist) : length (n::l) = length l + 1
  := rfl

theorem length_append (l₁ l₂ : natlist)
  : length (l₁ ++ l₂) = (length l₁) + (length l₂) :=
begin
  induction l₁ with n l ih,
    rw nil_append,
    rw length_nil,
    rw zero_add,
  rw cons_append,
  rw [length_cons, length_cons],
  rw ih,
  rw [add_assoc _ 1, add_comm 1, add_assoc],
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

theorem length_reverse (l: natlist) : length (reverse l) = length l :=
begin
  induction l with n l ih,
    refl,
  rw reverse,
  rw length_append,
  rw [length_cons, length_cons],
  rw length_nil,
  rw ih,
end

/-
(*  Search rev. *)
-/

/-
  not great, but
  ctrl+p #
-/

#print prefix lists

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

theorem append_nil (l : natlist) : l ++ [] = l :=
begin
  induction l with n l ih,
    refl,
  rw cons_append,
  rw ih,
end

#print prefix list

theorem reverse_append (l₁ l₂ : natlist)
  : reverse (l₁ ++ l₂) = reverse l₂ ++ reverse l₁ :=
begin
  induction l₁ with n l₁ ih,
    rw nil_append,
    rw reverse,
    rw append_nil,
  rw cons_append,
  rw [reverse, reverse],
  rw ih,
  rw append_assoc,
end

theorem reverse_involutive (l : natlist) : reverse (reverse l) = l :=
begin
  induction l with n l ih,
    refl,
  rw reverse,
  rw reverse_append,
  rw ih,
  refl,
end

/-
Theorem app_assoc4 : ∀l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem append_assoc4 (l₁ l₂ l₃ l₄ : natlist)
  : l₁ ++ (l₂ ++ (l₃ ++ l₄)) = ((l₁ ++ l₂) ++ l₃) ++ l₄ :=
by rw [append_assoc, append_assoc]

/-
Lemma nonzeros_app : ∀l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
-/

/-
TODO: explain rwa
-/

lemma nonzeros_append (l₁ l₂ : natlist) :
  nonzeros (l₁ ++ l₂) = (nonzeros l₁) ++ (nonzeros l₂) :=
begin
  induction l₁ with n l₁ ih,
    refl,
  cases n,
    rw cons_append,
    rwa [nonzeros, nonzeros],
  rw cons_append,
  rw [nonzeros, nonzeros],
  rw ih,
  rw cons_append,
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

def eqblist : natlist → natlist → bool
| nil nil := tt
| (h₁::t₁) (h₂::t₂) := if eqb h₁ h₂
                       then eqblist t₁ t₂
                       else ff
| _ _ := ff

example : eqblist nil nil := rfl

example : eqblist [1, 2, 3] [1, 2, 3] := rfl

example : eqblist [1, 2, 3] [1, 2, 4] = ff := rfl

lemma eqb_refl (l : ℕ) : eqb l l = tt :=
begin
  induction l with h l ih,
    refl,
  rwa eqb,
end

theorem eqblist_refl (l : natlist) : eqblist l l = tt :=
begin
  induction l with n l ih,
    refl,
  rw eqblist,
  rw eqb_refl,
  rw ih,
  refl,
end

/-
Theorem count_member_nonzero : ∀(s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem count_member_nonzero (s : bag) : 1 ≤? (count 1 (1 :: s)) = tt :=
begin
  induction s with n s ih,
    refl,
  refl,
end

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

theorem leb_succ (n : ℕ) : n ≤? succ n = tt :=
begin
  induction n with n ih,
    refl,
  rwa leb,
end

/-
Theorem remove_does_not_increase_count: ∀(s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem count_remove_leb_count (s : bag)
  : count 0 (remove_one 0 s) ≤? count 0 s = tt :=
begin
  induction s with h t ih,
    refl,
  cases h,
    rw remove_one,
    rw count,
    rw [function.comp_app, function.comp_app],
    rw filter,
    rw eqb,
    rw [if_pos rfl, if_pos rfl],
    rw length,
    rw leb_succ,
  /- not really sure why this works -/
  exact ih,
end

/-
∀(l1 l2 : natlist), rev l1 = rev l2 → l1 = l2.
-/

/-
TODO: revisit hard way as these tactics shouldn't be known yet
-/

lemma eq_append_nil_false
  (h : ℕ) (t : natlist) (c : t ++ [h] = nil) : false :=
begin
  have : length (t ++ [h]) = length (nil),
    exact congr_arg length c,
  rw length_append at this,
  rw length at this,
  rw length_nil at this,
  contradiction,
end

lemma eq_nil_append_false
  (h : ℕ) (t : natlist) (c : nil = t ++ [h]) : false :=
eq_append_nil_false h t (eq.symm c)

theorem snoc_injective' {h₁ h₂ : ℕ} : ∀ t₁ t₂ : natlist,
  t₁ ++ [h₁] = t₂ ++ [h₂] → h₁ = h₂ ∧ t₁ = t₂
| nil nil :=
begin
  intro h,
  injection h with hl hr,
  exact ⟨hl, hr⟩,
end
| (h₁'::t₁) nil :=
begin
  intro h,
  injection h with hl hr,
  exfalso,
  exact eq_append_nil_false _ _ hr,
end
| nil (h₂'::t₂) :=
begin
  intro h,
  injection h with hl hr,
  exfalso,
  exact eq_nil_append_false _ _ hr,
end
| (h₁'::t₁) (h₂'::t₂) :=
begin
  intro h,
  injection h with hl hr,
  have : h₁ = h₂ ∧ t₁ = t₂,
    exact snoc_injective' t₁ t₂ hr,
  split,
    rw this.left,
  rw [hl, this.right],
end

theorem reverse_injective_hard' :
  ∀ l₁ l₂ : natlist, reverse l₁ = reverse l₂ → l₁ = l₂
| nil nil :=
begin
  intro h,
  refl,
end
| nil (h₂::t₂) :=
begin
  intro h,
  rw [reverse, reverse] at h,
  exfalso,
  exact eq_nil_append_false _ _ h,
end
| (h₁::t₁) nil :=
begin
  intro h,
  rw [reverse, reverse] at h,
  exfalso,
  exact eq_append_nil_false _ _ h,
end
| (h₁::t₁) (h₂::t₂) :=
begin
  simp,
  intro h,
  have : h₁ = h₂ ∧ reverse t₁ = reverse t₂,
    exact snoc_injective' (reverse t₁) (reverse t₂) h,
  exact ⟨this.left, reverse_injective_hard' t₁ t₂ this.right⟩,
end

/-
without computation engine
-/
theorem snoc_injective {h₁ h₂ : ℕ} : ∀ t₁ t₂ : natlist,
  t₁ ++ [h₁] = t₂ ++ [h₂] → h₁ = h₂ ∧ t₁ = t₂ :=
begin
  intro t₁,
  induction t₁ with h₁' t₁ ih,
    rintro (_ | ⟨h₂', t₂⟩) h,
      injection h with hl hr,
      exact ⟨hl, hr⟩,
    injection h with hl hr,
    exfalso,
    exact eq_nil_append_false _ _ hr,
  rintro (_ | ⟨h₂', t₂⟩) h,
    injection h with hl hr,
    exfalso,
    exact eq_append_nil_false _ _ hr,
  injection h with hl hr,
  have : h₁ = h₂ ∧ t₁ = t₂,
    exact ih t₂ hr,
  split,
    exact this.left,
  rw [hl, this.right],
end

theorem reverse_injective_hard :
  ∀ l₁ l₂ : natlist, reverse l₁ = reverse l₂ → l₁ = l₂ :=
begin
  intro l₁,
  induction l₁ with h₁ t₁ ih,
    rintro (_ | ⟨h₂, t₂⟩) h,
      refl,
    rw [reverse, reverse] at h,
    exfalso,
    exact eq_nil_append_false _ _ h,
  rintro (_ | ⟨h₂, t₂⟩) h,
    rw [reverse, reverse] at h,
    exfalso,
    exact eq_append_nil_false _ _ h,
  rw [reverse, reverse] at h,
  have : h₁ = h₂ ∧ reverse t₁ = reverse t₂,
    exact snoc_injective (reverse t₁) (reverse t₂) h,
  rw this.left,
  have, exact ih _ this.right,
  rw this,
end

/-
now, for the easy way
-/

theorem reverse_injective
  (l₁ l₂ : natlist) (h : reverse l₁ = reverse l₂) : l₁ = l₂ :=
begin
  rw ←reverse_involutive l₁,
  rw ←reverse_involutive l₂,
  rw h,
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

example : nth_error [4, 5, 6, 7] 0 = some 4 := rfl

example : nth_error [4, 5, 6, 7] 3 = some 7 := rfl

example : nth_error [4, 5, 6, 7] 9 = none := rfl

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

def head_error : natlist → natoption
| nil := none
| (h::_) := some h

example : head_error [] = none := rfl

example : head_error [1] = some 1 := rfl

example : head_error [5, 6] = some 5 := rfl

/-
Theorem option_elim_hd : ∀(l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem option_elim_head (l : natlist) (default : ℕ)
  : head default l = option_elim default (head_error l) :=
begin
  cases l with n l,
    refl,
  refl,
end

/-
Inductive id : Type :=
  | Id (n : nat).
-/

/-
TODO: investigate error with using sf casing
-/
inductive Id : Type
| id (n : ℕ)

open Id

/-
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 ⇒ n1 =? n2
  end.
-/

def eqb_id : Id → Id → bool
| (id n₁) (id n₂) := n₁ =? n₂

/-
Theorem eqb_id_refl : ∀x, true = eqb_id x x.
Proof.
  (* FILL IN HERE *) Admitted.
-/

theorem eqb_id_refl (x : Id) : eqb_id x x = tt :=
begin
  cases x,
  rw eqb_id,
  rw eqb_refl,
end

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
  find x (update d x v) = some v :=
begin
  rw update,
  rw find,
  rw eqb_id_refl,
  refl,
end

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
begin
  rw update,
  rw find,
  rw h,
  refl,
end

/-
Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).
-/

/- you can write it, but can't make any -/
inductive baz : Type
| Baz1 (x : baz)
| Baz2 (y : baz) (b : bool)

end lists
