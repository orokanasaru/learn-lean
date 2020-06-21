import data.nat.basic
import .ch01_basics

open basics (evenb oddb sub_two leb)
open nat (add mul)

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

/- needing to already move to gadt syntax is annoying -/
inductive list (α : Type) : Type
| nil : list
| cons (a : α) (l : list) : list

open poly.list

/-
Check list.
(* ===> list : Type -> Type *)
-/

#check list

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

def repeat (α : Type) (a : α) : ℕ → list α
| 0 := nil
| (n + 1) := cons a (repeat n)

/-
Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
-/

example : repeat ℕ 4 2 = cons 4 (cons 4 nil) := rfl

/-
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.
-/

example : repeat bool ff 1 = cons ff nil := rfl

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
namespace mumble_grumble

inductive mumble : Type
| a
| b (x : mumble) (y : ℕ)
| c

inductive grumble (α : Type) : Type
| d (m : mumble) : grumble
| e (a : α) : grumble

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

def repeat' (α a) : ∀count, list α
| 0 := nil
| (count + 1) := cons a (repeat' count)

/-
Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)
-/

/-
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 ⇒ nil _
  | S count' ⇒ cons _ x (repeat'' _ x count')
  end.
-/

def repeat'' {α} (a) : ∀count, list α
| 0 := @nil _
| (count + 1) := cons a (repeat'' count)

/-
Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
-/

def list123 := cons 1 (cons 2 (cons 3 nil))

/-
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
-/

def list123' := @cons _ 1 (@cons _ 2 (@cons _ 3 (@nil _)))

/-
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
-/

/-
arguments doesn't appear to exist in lean
-/

/-
let's go one step further
-/

variables {α β γ : Type}

/-
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 ⇒ nil
  | S count' ⇒ cons x (repeat''' x count')
  end.
-/

/-
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
-/

inductive list' : Type
| nil' : list'
| cons' : α → list'

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

/-
to add something beyond polymorphism to this chapter,
let's also use generalized field notation
-/
def list.append : list α → list α → list α
| nil l₂ := l₂
| (cons h t) l₂ := cons h (t.append l₂)

def list.reverse : list α → list α
| nil := nil
| (cons h t) := t.reverse.append (cons h nil)

def list.length : list α → ℕ
| nil := 0
| (cons _ t) := t.length + 1

example :
  (cons 1 (cons 2 nil)).reverse = cons 2 (cons 1 nil) := rfl

example : (cons tt nil).reverse = cons tt nil := rfl

example : (cons 1 (cons 2 (cons 3 nil))).length = 3 := rfl

/-
Definition mynil : list nat := nil.
-/

def mynil : list ℕ := nil

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

local infixr :: := cons
local notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l
local infixr ++ := list.append

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

theorem cons_append (a : α) (l₁ l₂) : (a::l₁) ++ l₂ = a::(l₁ ++ l₂) := rfl

theorem append_nil (l : list α) : l ++ [] = l :=
begin
  induction l with a l ih,
    refl,
  rw cons_append,
  rw ih,
end

theorem nil_append (l : list α) : [] ++ l = l := rfl

theorem append_assoc (l m n : list α) : l ++ (m ++ n) = (l ++ m) ++ n :=
begin
  induction l with a l ih,
    refl,
  rw [cons_append, cons_append, cons_append],
  rw ih,
end

theorem length_nil : (@nil α).length = 0 := rfl

theorem length_cons (a : α) (l) : (a::l).length = l.length + 1 := rfl

lemma length_append (l₁ l₂ : list α) :
  (l₁ ++ l₂).length = l₁.length + l₂.length :=
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
Theorem rev_app_distr: ∀X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : ∀X : Type, ∀l : list X,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.
-/

open poly.list (reverse)

theorem reverse_append (l₁ l₂ : list α) :
  (l₁ ++ l₂).reverse = l₂.reverse ++ l₁.reverse :=
begin
  induction l₁ with a l₁ ih,
    rw nil_append,
    rw reverse,
    rw append_nil,
  rw cons_append,
  rw [reverse, reverse],
  rw ih,
  rw append_assoc,
end

theorem reverse_involutive (l : list α) : reverse (reverse l) = l :=
begin
  induction l with n l ih,
    refl,
  rw reverse,
  rw reverse_append,
  rw ih,
  refl,
end

/-
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.
-/

/- something else new -/
structure prod (α β : Type) : Type := (fst : α) (snd : β)

open poly.prod

/-
Notation "( x , y )" := (pair x y).
-/

/-
this is going to break (update : yep, {} break typeclass stuff)
local should be fine though
i don't see anything like coq's scope in lean
-/
local notation {x, y} := prod.mk x y
local infix × := prod

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

#check fst
#check snd

/-
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ ⇒ []
  | _, [] ⇒ []
  | x :: tx, y :: ty ⇒ (x, y) :: (combine tx ty)
  end.
-/

def combine : list α → list β → list (α × β)
| [] _ := []
| (a::ta) [] := []
| (a::ta) (b::tb) := {a, b}::combine ta tb

/-
Compute (combine [1;2] [false;false;true;true]).
-/

#check @combine
#reduce combine [1, 2] [ff, ff, tt, tt]

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
def split' : list (α × β) → list α × list β
| [] := {[], []}
| ({a, b}::l) := {a::(split' l).fst, b::(split' l).snd}

/- can also uses explicit induction to clearly be linear -/
def split (l : list (α × β)) : list α × list β :=
begin
  induction l with h t ih,
    exact {[], []},
  exact {h.fst::ih.fst, h.snd::ih.snd},
end

example : split [{1, ff}, {2, ff}] = {[1, 2], [ff, ff]} := rfl

/-
Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.
-/

inductive option (α : Type) : Type
| none : option
| some (a : α) : option

open poly.option

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

def nth_error : list α → ℕ → option α
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

def hd_error : list α → option α
| [] := none
| (h::_) := some h

/-
Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
 (* FILL IN HERE *) Admitted.
-/

#check @hd_error

example : hd_error [1,2] = some 1 := rfl

example : hd_error [[1], [2]] = some [1] := rfl

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

example : doit3times sub_two 9 = 3 := rfl

example : doit3times bnot tt = ff := rfl

/-
Fixpoint filter {X:Type} (test: X→bool) (l:list X)
                : (list X) :=
  match l with
  | [] ⇒ []
  | h :: t ⇒ if test h then h :: (filter test t)
                        else filter test t
  end.
-/

def list.filter {α : Type} (test : α → bool)
  : list α → list α
| [] := []
| (h::t) := if test h then h::t.filter else t.filter

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

example : [1, 2, 3, 4].filter evenb = [2,4] := rfl

def length_is_1 {α : Type} (l : list α) : bool :=
  list.length l =? 1

example : [[1, 2], [3], [4], [5, 6, 7], [], [8]].filter length_is_1
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

open poly.list (filter length)

def countoddmembers := length ∘ (filter oddb)

example : countoddmembers [1, 0, 3, 1, 4, 5] = 4 := rfl

example : countoddmembers [0,2,4] = 0 := rfl

example : countoddmembers [] = 0 := rfl

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

example :
  [[1, 2], [3], [4], [5, 6, 7], [], [8]].filter (λ l, l.length =? 1)
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
  filter_even_gt₇ [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8] := rfl

example : filter_even_gt₇ [5, 2, 6, 19, 129] = [] := rfl

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

def list.partition (test : α → bool) : list α → list α × list α
| [] := {[], []}
| (h::t) := if test h
            then {h::t.partition.fst, t.partition.snd}
            else {t.partition.fst, h::t.partition.snd}

example :
  [1,2,3,4,5].partition oddb = {[1, 3, 5], [2, 4]} := rfl

example :
  [5,9,0].partition (λ _, ff) = {[], [5, 9, 0]} := rfl

/-
Fixpoint map {X Y: Type} (f:X→Y) (l:list X) : (list Y) :=
  match l with
  | [] ⇒ []
  | h :: t ⇒ (f h) :: (map f t)
  end.
-/

def list.map (f : α → β) : list α → list β
| [] := []
| (h::t) := f h :: t.map

/-
Example test_map1: map (fun x ⇒ plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
-/

example : [2, 0, 2].map (λx, 3 + x) = [5, 3, 5] := rfl

/-
Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
-/

example : [2, 1, 2, 5].map oddb = [ff, tt, ff, tt] := rfl

/-
Example test_map3:
    map (fun n ⇒ [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.
-/

example : [2, 1, 2, 5].map (λn, [evenb n, oddb n])
  = [[tt, ff], [ff, tt], [tt, ff], [ff, tt]] := rfl

/-
Theorem map_rev : ∀(X Y : Type) (f : X → Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
-/

open poly.list (map)

lemma map_append (f : α → β) (l₁ l₂ : list α) :
  (l₁ ++ l₂).map f = l₁.map f ++ l₂.map f :=
begin
  induction l₁ with a l₁ ih,
    refl,
  rw cons_append,
  rw [map, map],
  rw ih,
  rw cons_append,
end

def map_reverse (f : α → β) (l : list α) :
  l.reverse.map f = (l.map f).reverse :=
begin
  induction l with a l ih,
    refl,
  rw map,
  rw [reverse, reverse],
  rw map_append,
  rw ih,
  refl,
end

/-
Fixpoint flat_map {X Y: Type} (f: X → list Y) (l: list X)
                   : (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_flat_map1:
  flat_map (fun n ⇒ [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
-/

/- i don't love the order that lean uses -/
def list.bind : list α → (α → list β) → list β
| [] f := []
| (h::t) f := f h ++ t.bind f

example : [1, 5, 4].bind (λn, [n, n, n])
  = [1, 1, 1, 5, 5, 5, 4, 4, 4] := rfl

/-
Definition option_map {X Y : Type} (f : X → Y) (xo : option X)
                      : option Y :=
  match xo with
    | None ⇒ None
    | Some x ⇒ Some (f x)
  end.
-/

def option.bind : option α → (α → β) → option β
| none f := none
| (some a) f := some (f a)

/-
Fixpoint fold {X Y: Type} (f: X→Y→Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil ⇒ b
  | h :: t ⇒ f h (fold f t b)
  end.
-/

def list.foldr (f: α → β → β) (b : β) : list α → β
| [] := b
| (a::t) := f a t.foldr

def list.foldl (f: α → β → α) : α → list β → α
| a [] := a
| a (b::t) := t.foldl (f a b)

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

open poly.list (foldr)

#check foldr band

example : [1, 2, 3, 4].foldr mul 1 = 24 := rfl

example : [tt, tt, ff, tt].foldr band tt = ff := rfl

/-
why is this ambiguous?
type class resolution fails if using has_append.append
-/
example : [[1], [], [2, 3], [4]].foldr list.append [] = [1, 2, 3, 4] := rfl

/-
Definition constfun {X: Type} (x: X) : nat→X :=
  fun (k:nat) ⇒ x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
-/

def constfun (a: α) : ℕ → α := λ_, a

def ftrue := constfun tt

example : ftrue 0 = tt := rfl

example : constfun 5 99 = 5 := rfl

/-
Check plus.
(* ==> nat -> nat -> nat *)
-/

#check add

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

def add₃ := add 3

example : add₃ 4 = 7 := rfl

example : doit3times add₃ 0 = 9 := rfl

example : doit3times (add 3) 0 = 9 := rfl

/-
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n ⇒ S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
-/

def fold_length (l : list α) : ℕ := l.foldr (λ_ n, n + 1) 0

example : fold_length [4, 7, 0] = 3 := rfl

/-
Theorem fold_length_correct : ∀X (l : list X),
  fold_length l = length l.
Proof.
(* FILL IN HERE *) Admitted.
-/

theorem fold_length_correct (l : list α) : fold_length l = l.length :=
begin
  induction l with a l ih,
    refl,
  rw length,
  rw fold_length at ih ⊢,
  rw foldr,
  rw ih,
end

/-
Definition fold_map {X Y: Type} (f: X → Y) (l: list X) : list Y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def fold_map (f : α → β) (l : list α) : list β :=
  l.foldr (λ h b, f h :: b) []

theorem fold_map_correct (f : α → β) (l : list α) :
  fold_map f l = l.map f :=
begin
  induction l with h t ih,
    refl,
  rw map,
  rw fold_map at ih ⊢,
  rw foldr,
  rw ih,
end

/-
Definition prod_curry {X Y Z : Type}
  (f : X * Y → Z) (x : X) (y : Y) : Z := f (x, y).
-/

def function.curry (f : α × β → γ) (a : α) (b : β) : γ := f {a, b}

/-
Definition prod_uncurry {X Y Z : Type}
  (f : X → Y → Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
-/

def function.uncurry (f : α → β → γ) (p : α × β) : γ := f p.fst p.snd

/-
Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
-/

example : [2, 0, 2].map (add 3) = [5, 3, 5] := rfl

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

open poly.function

#check @curry
#check @uncurry

theorem uncurry_curry (f : α → β → γ) (a : α) (b : β) :
  curry (uncurry f) a b = f a b := rfl

theorem curry_uncurry (f : α × β → γ) (p : α × β) :
  uncurry (curry f) p = f p :=
begin
  cases p with a b,
  refl,
end

/-
Definition cnat := ∀X : Type, (X → X) → X → X.
-/

def cnat := ∀α : Type, (α → α) → α → α

/-
Definition one : cnat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ f x.
-/

def one : cnat := λ_ f, f

/-
Definition two : cnat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ f (f x).
-/

def two : cnat := λ_ f, f ∘ f

/-
Definition zero : cnat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ x.
-/

def zero : cnat := λ_ f x, x

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
  λα f x, f (n α f x)

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
  λα f x, m α f (n α f x)

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
  λα f x, m α (n α f) x

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
  λα f x, n (α → α) (m α) f x

example : ex two two = plus two two := rfl

example : ex three zero = one := rfl

example : ex three two =
  plus (mult two (mult two two)) one := rfl

end poly
