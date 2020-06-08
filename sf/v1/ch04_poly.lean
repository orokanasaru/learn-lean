import data.nat.basic
import .ch01_basics

namespace poly

/-
Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).
-/

inductive boollist : Type
| bool_nil
| bool_cons (b : bool) (l : boollist)

/-
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
-/

/- can not shadow list -/
/- needing to already move to this syntax is annoying -/
inductive lst (X: Type) : Type
| nil : lst
| cons (x : X) (l : lst) : lst

open lst

/-
Check list.
(* ===> list : Type -> Type *)
-/

#check lst

/-
Check (nil nat).
(* ===> nil nat : list nat *)
-/

#check @nil ℕ

/-
Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)
-/

#check (cons 3 nil)

/-
Check nil.
(* ===> nil : forall X : Type, list X *)
-/

#check nil

/-
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)
-/

#check cons

/-
Check (cons nat 2 (cons nat 1 (nil nat))).
-/

#check (cons 2 (cons 1 nil))

/-
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 ⇒ nil X
  | S count' ⇒ cons X x (repeat X x count')
  end.
-/

def repeat {X : Type} (x : X) : ℕ → lst X
| 0 := nil
| (n + 1) := cons x (repeat n)

/-
Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
-/

example : repeat 4 2 = cons 4 (cons 4 nil) := rfl

/-
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.
-/

example : repeat ff 1 = cons ff nil := rfl

/-
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).
-/

/- i don't want to lose the ability to use a/b in prod -/
section mumble_grumble

inductive mumble : Type
| a
| b (x : mumble) (y : ℕ)
| c

inductive grumble (X : Type) : Type
| d (m : mumble) : grumble
| e (x : X) : grumble

open mumble
open grumble

#check d (b a 5)
#check @d mumble (b a 5)
#check @d bool (b a 5)
#check @e mumble (b c 0)
-- #check @e bool (b c 0)
#check c

end mumble_grumble

/-
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 ⇒ nil X
  | S count' ⇒ cons X x (repeat' X x count')
  end.
-/

/-
Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)
-/

/- need to go back and clean up implicits before this point -/
/- lean does not have type inference for parameters -/

/-
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 ⇒ nil _
  | S count' ⇒ cons _ x (repeat'' _ x count')
  end.
-/

/- if you hate yourself, i guess you can do this in lean -/
def repeat'' {X : Type} (x : X) : ∀ n : ℕ, lst X
| 0 := @nil _
| (n + 1) := @cons _ x (@repeat _ x n)

/-
Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
-/

def list123 := cons 1 (cons 2 (cons 3 nil))

/-
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
-/

/- again, why? -/

def list123' := @cons _ 1 (@cons _ 2 (@cons _ 3 (@nil _)))

/-
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
-/

/-
doesn't appear to exist in lean
something something metavariables
-/

/-
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 ⇒ nil
  | S count' ⇒ cons x (repeat''' x count')
  end.
-/

/- yeah, that how i defined it originally -/

/-
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
-/

inductive list' {X : Type} : Type
| nil' : list'
| cons' : X → list'

/-
Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil ⇒ l2
  | cons h t ⇒ cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil ⇒ nil
  | cons h t ⇒ app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil ⇒ 0
  | cons _ l' ⇒ S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.
-/

@[simp]
def app {α : Type} : lst α → lst α → lst α
| nil l₂ := l₂
| (cons h t) l₂ := cons h (app t l₂)

@[simp]
def rev {α : Type} : lst α → lst α
| nil := nil
| (cons h t) := app (rev t) (cons h nil)

@[simp]
def length {α : Type} : lst α → ℕ
| nil := 0
| (cons _ t) := length t + 1

example :
  rev (cons 1 (cons 2 nil)) = cons 2 (cons 1 nil) := rfl

example : rev (cons tt nil) = cons tt nil := rfl

example : length (cons 1 (cons 2 (cons 3 nil))) = 3 := rfl

/-
Definition mynil : list nat := nil.
-/

def mynil : lst ℕ := nil

/-
Check @nil.
Definition mynil' := @nil nat.
-/

#check @nil
def mynil' := @nil ℕ

/-
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
-/

infixr ` :: ` := cons
notation `⟦` l:(foldr `, ` (h t, cons h t) nil `⟧`) := l
infixr ` ++ ` := app

/-
Theorem app_nil_r : ∀(X:Type), ∀l:list X,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem app_assoc : ∀A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma app_length : ∀(X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem app_nil_r {α : Type} (l : lst α) :
  l ++ ⟦⟧ = l := by induction l; simp *

theorem app_assoc {α : Type} (l m n : lst α) :
  l ++ (m ++ n) = (l ++ m) ++ n := by induction l; simp *

/- want this later. don't want lst stuff -/

@[simp]
lemma app_length {α : Type} (l₁ l₂ : list α) :
  list.length (l₁ ++ l₂) = list.length l₁ + list.length l₂ :=
by induction l₁; simp [*, add_assoc, add_comm 1]

/-
Theorem rev_app_distr: ∀X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem rev_involutive : ∀X : Type, ∀l : list X,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

@[simp]
theorem rev_app_distr {α : Type} (l₁ l₂ : lst α) :
  rev (l₁ ++ l₂) = rev l₂ ++ rev l₁ :=
by induction l₁; simp [*, app_assoc]

@[simp]
theorem rev_involutive {α : Type} (l : lst α) :
  rev (rev l) = l := by induction l; simp *

/-
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.
-/

/- also reserved -/
inductive prod' (α β : Type) : Type
| pair (a : α) (b : β) : prod'

open prod'

/-
Notation "( x , y )" := (pair x y).
-/

/-
this is going to break (update : yep, {} break typeclass stuff)
i don't see anything like coq's scope in lean
-/
notation `⦃` x , y `⦄` := pair x y
infix ` * ` := prod'

/-
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) ⇒ x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) ⇒ y
  end.
-/

@[simp]
def fst {α β : Type} : α * β → α
| ⦃a, _⦄ := a

@[simp]
def snd {α β : Type} : α * β → β
| ⦃_, b⦄ := b

/-
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ ⇒ []
  | _, [] ⇒ []
  | x :: tx, y :: ty ⇒ (x, y) :: (combine tx ty)
  end.
-/

@[simp]
def combine {α β : Type} : lst α → lst β → lst (α * β)
| ⟦⟧ _ := ⟦⟧
| _ ⟦⟧ := ⟦⟧
| (a::ta) (b::tb) := ⦃a, b⦄ :: combine ta tb

/-
Compute (combine [1;2] [false;false;true;true]).
-/

#check @combine
#reduce combine ⟦1,2⟧ ⟦ff,ff,tt,tt⟧

/-
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* FILL IN HERE *) Admitted.
-/

/- lean caches so this won't be exponential -/
/- unfortunately lean seems incapable of unfolding this -/
def split' {α β : Type} : lst (α * β) → lst α * lst β
| ⟦⟧ := ⦃⟦⟧, ⟦⟧⦄
| (⦃a, b⦄::l) := ⦃a::fst (split' l), b::snd (split' l)⦄

/- can also uses explicit induction to clearly be linear -/
@[simp]
def split {α β : Type} (l : lst (α * β)) : lst α * lst β :=
begin
  induction l with h t ih,
    exact ⦃⟦⟧, ⟦⟧⦄,
  exact ⦃fst h::fst ih, snd h::snd ih⦄
end

example : split ⟦⦃1,ff⦄, ⦃2,ff⦄⟧ = ⦃⟦1,2⟧, ⟦ff,ff⟧⦄ := rfl

/-
Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.
-/

section option_playground

inductive opt (α : Type) : Type
| some (a : α) : opt
| none : opt

end option_playground

/-
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] ⇒ None
  | a :: l' ⇒ if n =? O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].

Example test_nth_error3 : nth_error [true] 2 = None.

-/

/- using real list again -/

def nth_error {α : Type} : list α → ℕ → option α
| [] _ := none
| (h::_) 0 := some h
| (_::t) (n + 1) := nth_error t n

example : nth_error [4,5,6,7] 0 = some 4 := rfl

example : nth_error [[1],[2]] 1 = some [2] := rfl

example : nth_error [tt] 2 = none := rfl

/-
Definition hd_error {X : Type} (l : list X) : option X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def hd_error {α : Type} : list α → option α
| [] := none
| (h::_) := h

/-
Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
 (* FILL IN HERE *) Admitted.
-/

#check @hd_error

example : hd_error [1,2] = some 1 := rfl

example : hd_error [[1],[2]] = some [1] := rfl

/-
Definition doit3times {X:Type} (f:X→X) (n:X) : X :=
  f (f (f n)).
-/

def doit3times {α : Type} (f: α → α) (n : α) : α :=
  f (f (f n))

/-
Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.
-/

#check @doit3times

example : doit3times minustwo 9 = 3 := rfl

example : doit3times negb tt = ff := rfl

/-
Fixpoint filter {X:Type} (test: X→bool) (l:list X)
                : (list X) :=
  match l with
  | [] ⇒ []
  | h :: t ⇒ if test h then h :: (filter test t)
                        else filter test t
  end.
-/

@[simp]
def filter {α : Type} (test : α → bool)
  : list α → list α
| [] := []
| (h::t) := if test h then h :: filter t else filter t

/-
Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.
-/

example : filter evenb [1,2,3,4] = [2,4] := rfl

def length_is_1 {α : Type} (l : list α) : bool :=
  list.length l =? 1

example : filter length_is_1
  [[1,2], [3], [4], [5,6,7], [], [8]]
  = [[3], [4], [8]] := rfl

/-
Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.
-/

/- pretty sure this is how i did it anyway -/
def countoddmembers := list.length ∘ (filter oddb)

example : countoddmembers [1,0,3,1,4,5] = 4 := rfl

example : countoddmembers [0,2,4] = 0 := rfl

example : countoddmembers list.nil = 0 := rfl

/-
Example test_anon_fun':
  doit3times (fun n ⇒ n * n) 2 = 256.
Proof. reflexivity. Qed.
-/

/- commenting out as this is murdering my computer... -/
-- example : doit3times (λ (n : int), n * n) 2 = 256 := rfl

/-
Example test_filter2':
    filter (fun l ⇒ (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.
-/

example : filter (λ l, list.length l =? 1)
  [[1,2], [3], [4], [5,6,7], [], [8]]
  = [[3], [4], [8]] := rfl

/-
Definition filter_even_gt7 (l : list nat) : list nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.
-/

def filter_even_gt₇ := filter (λ n, evenb n && leb 7 n)

example :
  filter_even_gt₇ [1,2,6,9,10,3,12,8] = [10,12,8] := rfl

example : filter_even_gt₇ [5,2,6,19,129] = [] := rfl

/-
Definition partition {X : Type}
                     (test : X → bool)
                     (l : list X)
                   : list X * list X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.

Example test_partition2: partition (fun x ⇒ false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.
-/

/- reminder: the translation will be linear -/
def partition {α : Type} (test : α → bool)
  : list α → list α × list α
| [] := ([], [])
| (h::t) := if test h
            then (h::(partition t).fst, (partition t).snd)
            else ((partition t).fst, h::(partition t).snd)

example :
  partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]) := rfl

example :
  partition (λ _, ff) [5,9,0] = ([], [5,9,0]) := rfl

/-
Fixpoint map {X Y: Type} (f:X→Y) (l:list X) : (list Y) :=
  match l with
  | [] ⇒ []
  | h :: t ⇒ (f h) :: (map f t)
  end.
-/

/-
using lst again as that's how rev is defined
induction on list.reverse is more difficult
-/

@[simp]
def map {α β : Type} (f : α → β) : lst α → lst β
| ⟦⟧ := ⟦⟧
| (h::t) := f h :: map t

/-
Example test_map1: map (fun x ⇒ plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
-/

example : map (λ x, 3 + x) ⟦2,0,2⟧ = ⟦5,3,5⟧ := rfl

/-
Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
-/

example : map oddb ⟦2,1,2,5⟧ = ⟦ff,tt,ff,tt⟧ := rfl

/-
Example test_map3:
    map (fun n ⇒ [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.
-/

example : map (λ n, [evenb n, oddb n]) ⟦2,1,2,5⟧
  = ⟦[tt,ff], [ff,tt], [tt,ff], [ff,tt]⟧ := rfl

/-
Theorem map_rev : ∀(X Y : Type) (f : X → Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
-/

lemma map_assoc
  {α β : Type} (f : α → β)
  (l₁ l₂ : lst α) :
  map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ :=
by induction l₁; simp *

def map_rev {α β : Type} (f : α → β) (l : lst α) :
  map f (rev l) = rev (map f l) :=
by induction l; simp [*, map_assoc]

/-
Fixpoint flat_map {X Y: Type} (f: X → list Y) (l: list X)
                   : (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_flat_map1:
  flat_map (fun n ⇒ [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
-/

def flat_map {α β : Type} (f : α → list β) :
  list α → list β
| [] := []
| (h::t) := f h ++ flat_map t

example : flat_map (λ n, [n,n,n]) [1,5,4]
  = [1,1,1,5,5,5,4,4,4] := rfl

/-
Definition option_map {X Y : Type} (f : X → Y) (xo : option X)
                      : option Y :=
  match xo with
    | None ⇒ None
    | Some x ⇒ Some (f x)
  end.
-/

def option_map {α β : Type} (f : α → β)
  : option α → option β
| none := none
| (some a) := some (f a)

/-
Fixpoint fold {X Y: Type} (f: X→Y→Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil ⇒ b
  | h :: t ⇒ f h (fold f t b)
  end.
-/

@[simp]
def fold {α β : Type} (f: α → β → β) :
  lst α → β → β
| ⟦⟧ b := b
| (h::t) b := f h (fold t b)

def fold' {α β : Type} (f: α → β → β) :
  lst α → β → β
| ⟦⟧ b := b
| (h::t) b := fold' t (f h b)

/-
Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
-/

#check fold andb

open NatPlayground2

example : fold mult ⟦1,2,3,4⟧ 1 = 24 := rfl

example : fold andb ⟦tt,tt,ff,tt⟧ tt = ff := rfl

example : fold app ⟦⟦1⟧, ⟦⟧, ⟦2,3⟧, ⟦4⟧⟧ ⟦⟧ = ⟦1,2,3,4⟧ := rfl

/-
Definition constfun {X: Type} (x: X) : nat→X :=
  fun (k:nat) ⇒ x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
-/

def constfun {α : Type} (a: α) : ℕ → α := λ _, a

def ftrue := constfun tt

example : ftrue 0 = tt := rfl

example : constfun 5 99 = 5 := rfl

/-
Check plus.
(* ==> nat -> nat -> nat *)
-/

#check plus

/-
Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.
-/

def plus₃ := plus 3

example : plus₃ 4 = 7 := rfl

example : doit3times plus₃ 0 = 9 := rfl

example : doit3times (plus 3) 0 = 9 := rfl

/-
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n ⇒ S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
-/

@[simp]
def fold_length {α : Type} (l : lst α) : ℕ :=
  fold (λ _ n, n + 1) l 0

example : fold_length ⟦4,7,0⟧ = 3 := rfl

/-
Theorem fold_length_correct : ∀X (l : list X),
  fold_length l = length l.
Proof.
(* FILL IN HERE *) Admitted.
-/

theorem fold_length_correct {α : Type} (l : lst α) :
  fold_length l = length l :=
begin
  induction l with h t ih,
    simp,
  simp,
  exact ih,
end

/-
Definition fold_map {X Y: Type} (f: X → Y) (l: list X) : list Y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

@[simp]
def fold_map {α β} (f : α → β) (l : lst α) : lst β :=
  fold (λ h b, f h :: b) l ⟦⟧

theorem fold_map_correct
  {α β : Type} (f : α → β) (l : lst α) :
  fold_map f l = map f l :=
begin
  induction l with h t ih,
    simp,
  simp,
  show fold_map f t = map f t,
  rw ih,
end

/-
Definition prod_curry {X Y Z : Type}
  (f : X * Y → Z) (x : X) (y : Y) : Z := f (x, y).
-/

@[simp]
def prod_curry {α β γ : Type}
  (f : α × β → γ) (a : α) (b : β) : γ := f (a, b)

/-
Definition prod_uncurry {X Y Z : Type}
  (f : X → Y → Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

@[simp]
def prod_uncurry {α β γ : Type}
  (f : α → β → γ) (p : α × β) : γ := f p.fst p.snd

/-
Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
-/

example : map (plus 3) ⟦2,0,2⟧ = ⟦5,3,5⟧ := rfl

/-
Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : ∀(X Y Z : Type)
                        (f : X → Y → Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : ∀(X Y Z : Type)
                        (f : (X * Y) → Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
-/

#check @prod_curry
#check @prod_uncurry

theorem uncurry_curry
  {α β γ : Type} (f : α → β → γ) (a : α) (b : β) :
  prod_curry (prod_uncurry f) a b = f a b := rfl

theorem curry_uncurry
  {α β γ : Type} (f : α × β → γ) (p : α × β) :
  prod_uncurry (prod_curry f) p = f p := by simp

/-
Definition cnat := ∀X : Type, (X → X) → X → X.
-/

def cnat := ∀ α : Type, (α → α) → α → α

/-
Definition one : cnat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ f x.
-/

def one : cnat := λ _ f, f

/-
Definition two : cnat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ f (f x).
-/

def two : cnat := λ _ f, f ∘ f

/-
Definition zero : cnat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ x.
-/

def zero : cnat := λ _ f x, x

/-
Definition three : cnat := @doit3times.
-/

def three : cnat := @doit3times

/-
Definition succ (n : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.
-/

def succ (n : cnat) : cnat :=
  λ α f x, f (n α f x)

example : succ zero = one := rfl

example : succ one = two := rfl

example : succ two = three := rfl

/-
Definition plus (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.
-/

def plus (m n : cnat) : cnat :=
  λ α f x, m α f (n α f x)

example : plus zero one = one := rfl

example : plus two three = plus three two := rfl

example : plus (plus two two) three
  = plus one (plus three three) := rfl

/-
Definition mult (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.
-/

def mult (m n : cnat) : cnat :=
  λ α f x, m α (n α f) x

example : mult one one = one := rfl

example : mult zero (plus three three) = zero := rfl

example : mult two three = plus three three := rfl

/-
Definition exp (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.
-/

/- exp is taken -/
/-
holy fuck, mind blowing even after
giving up and reading the wiki article
using untyped lambda calculus
-/
def ex (m n : cnat) : cnat :=
  λ α f x, n (α → α) (m α) f x

example : ex two two = plus two two := rfl

example : ex three zero = one := rfl

example : ex three two =
  plus (mult two (mult two two)) one := rfl

end poly
