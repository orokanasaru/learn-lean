import tactic.basic
import .ch11_imp

namespace impparser

/-
Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString ⇒ []
  | String c s ⇒ c :: (list_of_string s)
  end.

Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] ⇒ [] | _ :: _ ⇒ [rev acc] end in
  match xs with
  | [] ⇒ tk
  | (x :: xs') ⇒
    match cls, classifyChar x, x with
    | _, _, "(" ⇒
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")" ⇒
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _ ⇒
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x ⇒
      tokenize_helper alpha (x :: acc) xs'
    | digit,digit,x ⇒
      tokenize_helper digit (x :: acc) xs'
    | other,other,x ⇒
      tokenize_helper other (x :: acc) xs'
    | _,tp,x ⇒
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
    tokenize "abc12=3 223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.
-/

def isWhite (c : char) : bool :=
  let n := c.to_nat in
  (n = 32) || (n = 9) || (n = 10) || (n = 13)

def isLowerAlpha (c : char) : bool :=
  let n := c.to_nat in (97 ≤ n) && (n ≤ 122)

def isAlpha (c : char) : bool :=
  let n := c.to_nat in
  (65 ≤ n) && (n ≤ 90) || (97 ≤ n) && (n ≤ 122)

def isDigit (c : char) : bool :=
  let n := c.to_nat in (48 ≤ n) && (n ≤ 57)

inductive chartype | white | alpha | digit | other
open chartype

/-
TODO : file bug about whitespace on windows
-/

def classifyChar (c : char) :=
  if c.is_whitespace then white /- lean fails on crlf -/
  else if c.is_alpha then alpha
  else if c.is_digit then digit
  else other

def list_of_string (s: string) := s.data

def string_of_list (cs : list char) : string := ⟨cs⟩

def token := string

-- def tokenize_helper : list (list char) :=
--   λ(cls : chartype) (acc xs : list char),
--     list.rec_on xs tk (λx xs' ih, tk)
--     let tk := match acc with [] := [] | _ := [acc.reverse] end in

-- def tokenize_helper (cls : chartype) (acc xs : list char) : list (list char) :=
--   let tk := match acc with [] := [] | _ := [acc.reverse] end in
--   match xs with
--   | [] := tk
--   | x :: xs' :=
--     match cls, classifyChar x, x with
--       | _, _, '(' := tk ++ ['(']::tokenize_helper other [] xs'
--       | _, _, _ := tk
--     end
--   end

-- def tokenize_helper (cls : chartype) (acc xs : list char) : list (list char) :=
--   let tk := match acc with [] := [] | _ := [acc.reverse] end in
--   list.rec_on xs
--     (λ_ _, tk)
--     (λx xs' ih cls acc,
--       match cls, classifyChar x, x with
--         | _, _, '(' := tk ++ ['(']::ih other []
--         | _, _, ')' := tk ++ [')']::ih other []
--         | _, white, _ := tk ++ ih white []
--         | alpha, alpha, x := ih alpha (x :: acc)
--         | digit, digit, x := ih digit (x :: acc)
--         | other, other, x := ih other (x :: acc)
--         | _, tp, x := tk ++ ih tp [x]
--       end
--   ) cls acc

-- #print list.rec
-- #print list.rec_on

-- def tokenize_helper'' (cls : chartype) (acc xs : list char) : list (list char) :=
--   let tk := if acc ≠ [] then [] else [acc.reverse] in
--   xs.brec_on $ λxs b,
--     match xs with
--     | x :: xs := tk
--     | _ := tk
--     end

/-
i don't know how to make this nicer
-/

def rev_ll (ls : list char) := if ls = [] then [] else [ls.reverse]

def tokenize_helper : chartype → list char → list char → list (list char)
| cls acc [] := rev_ll acc
| cls acc (x :: xs') :=
  let tk := rev_ll acc in
  match cls, classifyChar x, x with
  | _, _, '(' := tk ++ ['(']::tokenize_helper other [] xs'
  | _, _, ')' := tk ++ [')']::tokenize_helper other [] xs'
  | _, white, _ := tk ++ tokenize_helper white [] xs'
  | alpha, alpha, x := tokenize_helper alpha (x :: acc) xs'
  | digit, digit, x := tokenize_helper digit (x :: acc) xs'
  | other, other, x := tokenize_helper other (x :: acc) xs'
  | _, tp, x := tk ++ tokenize_helper tp [x] xs'
  end

-- #print tokenize_helper
-- #print tokenize_helper._main

def tokenize (s) : list string :=
  list.map string_of_list (tokenize_helper white [] $ list_of_string s)

-- run_cmd mk_simp_attr `token_simp

-- attribute [token_simp]
--     tokenize list_of_string classifyChar list.map string_of_list
--     tokenize_helper tokenize_helper._match_1 tokenize_helper._match_2
--     tokenize_helper' tokenize_helper'._match_1 tokenize_helper'._match_2
--     tokenize_helper'._match_3 list.reverse list.reverse_core ite
--     has_le.le and or not eq and.decidable or.decidable decidable.rec
--     char.val
--     char.is_whitespace char.is_alpha char.is_upper char.is_lower char.is_digit

-- example : tokenize "" = [] := rfl

-- set_option pp.notation false
-- set_option pp.structure_projections false

-- example : tokenize_helper white [] ['a'] = [['a']] :=
-- begin
--   simp with token_simp,
--   refl
-- end

-- example : tokenize_helper white [] ['a', 'b'] = [['a', 'b']] := rfl
-- example : tokenize_helper white [] ['a', 'b', '1'] = [['a', 'b'], ['1']] := rfl

-- example : tokenize "a" = ["a"] := rfl

-- example : tokenize "abc12=3" = ["abc", "12", "=", "3"] := rfl

example : tokenize "abc12=3 223*(3+(a+c))" =
  ["abc", "12", "=", "3",
  "223", "*", "(", "3", "+", "(", "a", "+", "c", ")", ")"] := rfl

/-
Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.
-/

inductive optionE (α : Type)
| SomeE (a : α) : optionE
| NoneE (s : string) : optionE

open optionE

instance option_monad : monad optionE := {
  pure := λα, SomeE,
  bind := λα β a f,
    match a with
    | (SomeE e) := f e
    | (NoneE e) := NoneE e
    end
}

instance option_hasOrElse : has_orelse optionE := ⟨λα a b,
  match a with
  | (SomeE e) := SomeE e
  | (NoneE e) := b
  end
⟩

/-
Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p ⇒ e2
       | NoneE err ⇒ NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3"
   := (match e1 with
       | SomeE p ⇒ e2
       | NoneE _ ⇒ e3
       end)
   (right associativity, p pattern,
    at level 60, e1 at next level, e2 at next level).
-/

-- notation `' ` p:60 ` ← ` e₁:55 ` ;; ` e₂ :=
--   match e₁ with
--   | SomeE p := e₂
--   | NoneE err := NoneE err
--   end

-- notation `TRY ` ` ' ` p:60 ← e₁:55 ` ;; ` e₂:55 ` OR ` e₃ :=
--   match e₁ with
--   | SomeE p := e₂
--   | NoneE _ := e₃
--   end

/-
Open Scope string_scope.

Definition parser (T : Type) :=
  list token → optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ ⇒
      NoneE "Too many recursive calls"
  | _, NoneE _ ⇒
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') ⇒
      many_helper p (t :: acc) steps' xs'
  end.
-/

open nat

def parser (α : Type) := list token → optionE (α × list token)

def many_helper {α} (p : parser α) : list α → ℕ → parser (list α)
| _ 0 _ := NoneE "Too many recursive calls"
| acc (succ steps') xs :=
  match p xs with
  | (NoneE _) := SomeE (acc.reverse, xs)
  | (SomeE (t, xs')) := many_helper (t :: acc) steps' xs'
  end

/-
Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.
-/

def many {α} (p steps) : parser (list α) := many_helper p [] steps

/-
Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs ⇒ match xs with
            | x :: xs' ⇒
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] ⇒
              NoneE ("expected '" ++ t ++ "'.")
            end.
-/

def firstExpect {α} (t : token) (p : parser α) : parser α
| (x :: xs') := if x = t then p xs' else NoneE $ "expected '" ++ t ++ "'."
| [] := NoneE $ "expected '" ++ t ++ "'."

/-
Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs ⇒ SomeE (tt, xs)).
-/

def expect (t) : parser unit :=
  firstExpect t $ λxs, SomeE ((), xs)

/-
Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] ⇒ NoneE "Expected identifier"
| x :: xs' ⇒
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.
-/

def parseIdentifier : parser string
| [] := NoneE "Expected identifier"
| (x :: xs') :=
  if x.data.all isLowerAlpha
  then SomeE (x, xs')
  else NoneE ("Illegal identifier:'" ++ x ++ "'")

/-
Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] ⇒ NoneE "Expected number"
| x :: xs' ⇒
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d ⇒
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      NoneE "Expected number"
end.
-/

def parseNumber : parser ℕ
| [] := NoneE "Expected number"
| (x :: xs') :=
  if x.data.all isDigit
  then SomeE (x.data.foldl (λn d, 10 * n + d.val - '0'.val) 0, xs')
  else NoneE "Expected number"

/-
Fixpoint parsePrimaryExp (steps:nat)
                         (xs : list token)
                       : optionE (aexp * list token) :=
  match steps with
  | 0 ⇒ NoneE "Too many recursive calls"
  | S steps' ⇒
      TRY ' (i, rest) <- parseIdentifier xs ;;
          SomeE (AId i, rest)
      OR
      TRY ' (n, rest) <- parseNumber xs ;;
          SomeE (ANum n, rest)
      OR
      ' (e, rest) <- firstExpect "(" (parseSumExp steps') xs ;;
      ' (u, rest') <- expect ")" rest ;;
      SomeE (e,rest')
  end

with parseProductExp (steps:nat)
                     (xs : list token) :=
  match steps with
  | 0 ⇒ NoneE "Too many recursive calls"
  | S steps' ⇒
    ' (e, rest) <- parsePrimaryExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "*" (parsePrimaryExp steps'))
                          steps' rest ;;
    SomeE (fold_left AMult es e, rest')
  end

with parseSumExp (steps:nat) (xs : list token) :=
  match steps with
  | 0 ⇒ NoneE "Too many recursive calls"
  | S steps' ⇒
    ' (e, rest) <- parseProductExp steps' xs ;;
    ' (es, rest') <-
        many (fun xs ⇒
                TRY ' (e,rest') <-
                    firstExpect "+"
                                (parseProductExp steps') xs ;;
                    SomeE ( (true, e), rest')
                OR
                ' (e, rest') <-
                    firstExpect "-"
                                (parseProductExp steps') xs ;;
                SomeE ( (false, e), rest'))
        steps' rest ;;
      SomeE (fold_left (fun e0 term ⇒
                          match term with
                          | (true, e) ⇒ APlus e0 e
                          | (false, e) ⇒ AMinus e0 e
                          end)
                       es e,
             rest')
  end.

Definition parseAExp := parseSumExp.
-/

open imp imp.aexp

/- destroys need for using_well_founded and generalizes nicely -/
/-
TODO: this (or something like it) probably belongs in the library
-/

instance psum_sizeof {α β} [sa: has_sizeof α] [sb : has_sizeof β]
  : has_sizeof (psum α β) :=
begin
  unfreezeI,
  constructor,
  intro p,
  cases p,
    cases sa,
    exact sa p,
  cases sb,
  exact sb p,
end

/-
this is annoying.
TODO: is there a way to not need n ≤ succ n everywhere?
-/

mutual def parsePrimaryExp, parseProductExp, parseSumExp
with parsePrimaryExp : ℕ → parser aexp
| (succ steps) := λxs,
  have steps < succ steps, from lt_succ_self steps,
  (do (i, rest) ← parseIdentifier xs, pure (AId i, rest)) <|>
  (do (n, rest) ← parseNumber xs, pure (ANum n, rest)) <|>
  do
    (e, rest) ← firstExpect "(" (parseSumExp steps) xs,
    (u, rest') ← expect ")" rest,
    pure (e, rest')
| _ := λ_, NoneE "Too many recursive calls"

with parseProductExp : ℕ → parser aexp
| 0 := λ_, NoneE "Too many recursive calls"
| (succ steps) := λxs,
  have steps < succ steps, from lt_succ_self steps,
  do
    (e, rest) ← parsePrimaryExp steps xs,
    (es, rest') ← many (firstExpect "*" (parsePrimaryExp steps)) steps rest,
    pure (es.foldl AMult e, rest')

with parseSumExp : ℕ → parser aexp
| 0 := λ_, NoneE "Too many recursive calls"
| (succ steps) := λxs,
  have steps < succ steps, from lt_succ_self steps,
  do
    (e, rest) ← parseProductExp steps xs,
    (es, rest') ← many (λxs,
        (do
          (e, rest') ← firstExpect "+" (parseProductExp steps) xs,
          pure ((tt, e), rest')) <|>
        do
          (e, rest') ← firstExpect "-" (parseProductExp steps) xs,
          pure ((ff, e), rest')
      ) steps rest,
    pure (es.foldl (λe₀ term,
        match term with
        | (tt, e) := APlus e₀ e
        | (ff, e) := AMinus e₀ e
        end
      ) e, rest')

def parseAExp := parseSumExp

/-
Fixpoint parseAtomicExp (steps:nat)
                        (xs : list token) :=
match steps with
  | 0 ⇒ NoneE "Too many recursive calls"
  | S steps' ⇒
     TRY ' (u,rest) <- expect "true" xs ;;
         SomeE (BTrue,rest)
     OR
     TRY ' (u,rest) <- expect "false" xs ;;
         SomeE (BFalse,rest)
     OR
     TRY ' (e,rest) <- firstExpect "¬"
                                   (parseAtomicExp steps')
                                   xs ;;
         SomeE (BNot e, rest)
     OR
     TRY ' (e,rest) <- firstExpect "("
                                   (parseConjunctionExp steps')
                                   xs ;;
         ' (u,rest') <- expect ")" rest ;;
         SomeE (e, rest')
     OR
     ' (e, rest) <- parseProductExp steps' xs ;;
     TRY ' (e', rest') <- firstExpect "="
                                  (parseAExp steps') rest ;;
         SomeE (BEq e e', rest')
     OR
     TRY ' (e', rest') <- firstExpect "≤"
                                      (parseAExp steps') rest ;;
         SomeE (BLe e e', rest')
     OR
     NoneE "Expected '=' or '≤' after arithmetic expression"
end

with parseConjunctionExp (steps:nat)
                         (xs : list token) :=
  match steps with
  | 0 ⇒ NoneE "Too many recursive calls"
  | S steps' ⇒
    ' (e, rest) <- parseAtomicExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "&&"
               (parseAtomicExp steps'))
            steps' rest ;;
    SomeE (fold_left BAnd es e, rest')
  end.

Definition parseBExp := parseConjunctionExp.

Check parseConjunctionExp.

Definition testParsing {X : Type}
           (p : nat →
                list token →
                optionE (X * list token))
           (s : string) :=
  let t := tokenize s in
  p 100 t.
-/

open imp.bexp

mutual def parseAtomicExp, parseConjunctionExp
with parseAtomicExp : ℕ → parser bexp
| 0 := λ_, NoneE "Too many recursive calls"
| (succ steps) := λxs,
  have steps < succ steps, from lt_succ_self steps,
  (do (u, rest) ← expect "true" xs, return (BTrue, rest)) <|>
  (do (u, rest) ← expect "false" xs, return (BFalse, rest)) <|>
  (do
    (e, rest) ← firstExpect "¬" (parseAtomicExp steps) xs,
    return (BNot e, rest)) <|>
  (do
    (e, rest) ← firstExpect "(" (parseConjunctionExp steps) xs,
    (u, rest') ← expect ")" rest,
    return (e, rest')) <|>
  do
    (e, rest) ← parseProductExp steps xs,
    (do
      (e', rest') ← firstExpect "=" (parseAExp steps) rest,
      return (BEq e e', rest')) <|>
    (do
      (e', rest') ← firstExpect "≤" (parseAExp steps) rest,
      return (BLe e e', rest')) <|>
    NoneE "Expected '=' or '≤' after arithmetic expression"

with parseConjunctionExp : ℕ → parser bexp
| 0 := λ_, NoneE "Too many recursive calls"
| (succ steps) := λxs,
  have steps < succ steps, from lt_succ_self steps,
  do
    (e, rest) ← parseAtomicExp steps xs,
    (es, rest') ← many (firstExpect "&&" (parseAtomicExp steps)) steps rest,
    return (es.foldl BAnd e, rest')

def parseBExp := parseConjunctionExp

#check parseConjunctionExp

def testParsing {α : Type} (p : ℕ → parser α) (s) := p 100 $ tokenize s

def aexp_tos : aexp → string
| (ANum n) := has_repr.repr n
| (AId x) := x
| (APlus n m) := "(" ++ aexp_tos n ++ "+" ++ aexp_tos m ++ ")"
| (AMinus n m) := "(" ++ aexp_tos n ++ "-" ++ aexp_tos m ++ ")"
| (AMult n m) := "(" ++ aexp_tos n ++ "*" ++ aexp_tos m ++ ")"

instance aexp_repr : has_repr aexp := ⟨aexp_tos⟩

def bexp_tos : bexp → string
| BTrue := "true"
| BFalse := "false"
| (BEq a₁ a₂) := "(" ++ aexp_tos a₁ ++ "=" ++ aexp_tos a₂ ++ ")"
| (BLe a₁ a₂) := "(" ++ aexp_tos a₁ ++ "≤" ++ aexp_tos a₂ ++ ")"
| (BNot b₁) := "¬" ++ bexp_tos b₁
| (BAnd b₁ b₂) := "(" ++ bexp_tos b₁ ++ "&&" ++ bexp_tos b₂ ++ ")"

instance bexp_repr : has_repr bexp := ⟨bexp_tos⟩

instance option_repr {α} [has_repr α] : has_repr (optionE α) := ⟨λo,
  match o with
  | SomeE e := "Some: " ++ has_repr.repr e
  | NoneE e := "None: " ++ e
  end
⟩

instance token_repr : has_repr token := ⟨id⟩

#eval testParsing parseProductExp "x.y.(x.x).x"

#eval testParsing parseConjunctionExp "¬(x=x&&x*x≤(x*x)*x)&&x=x"

/-
Fixpoint parseSimpleCommand (steps:nat)
                            (xs : list token) :=
  match steps with
  | 0 ⇒ NoneE "Too many recursive calls"
  | S steps' ⇒
    TRY ' (u, rest) <- expect "SKIP" xs ;;
        SomeE (SKIP%imp, rest)
    OR
    TRY ' (e,rest) <-
            firstExpect "TEST"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "THEN"
                        (parseSequencedCommand steps') rest ;;
        ' (c',rest'') <-
            firstExpect "ELSE"
                        (parseSequencedCommand steps') rest' ;;
        ' (tt,rest''') <-
            expect "END" rest'' ;;
       SomeE(TEST e THEN c ELSE c' FI%imp, rest''')
    OR
    TRY ' (e,rest) <-
            firstExpect "WHILE"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "DO"
                        (parseSequencedCommand steps') rest ;;
        ' (u,rest'') <-
            expect "END" rest' ;;
        SomeE(WHILE e DO c END%imp, rest'')
    OR
    TRY ' (i, rest) <- parseIdentifier xs ;;
        ' (e, rest') <- firstExpect "::=" (parseAExp steps') rest ;;
        SomeE ((i ::= e)%imp, rest')
    OR
        NoneE "Expecting a command"
end

with parseSequencedCommand (steps:nat)
                           (xs : list token) :=
  match steps with
  | 0 ⇒ NoneE "Too many recursive calls"
  | S steps' ⇒
    ' (c, rest) <- parseSimpleCommand steps' xs ;;
    TRY ' (c', rest') <-
            firstExpect ";;"
                        (parseSequencedCommand steps') rest ;;
        SomeE ((c ;; c')%imp, rest')
    OR
    SomeE (c, rest)
  end.

Definition bignumber := 1000.

Definition parse (str : string) : optionE com :=
  let tokens := tokenize str in
  match parseSequencedCommand bignumber tokens with
  | SomeE (c, []) ⇒ SomeE c
  | SomeE (_, t :: _) ⇒ NoneE ("Trailing tokens remaining: " ++ t)
  | NoneE err ⇒ NoneE err
  end.
-/

open imp.com

mutual def parseSimpleCommand, parseSequencedCommand
with parseSimpleCommand : ℕ → parser com
| 0 := λ_, NoneE "Too many recursive calls"
| (succ steps) := λxs,
  have steps < succ steps, from lt_succ_self steps,
  do { (u, rest) ← expect "SKIP" xs, pure (SKIP, rest) } <|>
  do {
    (e, rest) ← firstExpect "TEST" (parseBExp steps) xs,
    (c, rest') ← firstExpect "THEN" (parseSequencedCommand steps) rest,
    (c', rest'') ← firstExpect "ELSE" (parseSequencedCommand steps) rest',
    ((), rest''') ← expect "END" rest'',
    pure (TEST e THEN c ELSE c' FI, rest''') } <|>
  do {
    (e, rest) ← firstExpect "WHILE" (parseBExp steps) xs,
    (c, rest') ← firstExpect "DO" (parseSequencedCommand steps) rest,
    (u, rest'') ← expect "END" rest',
    pure (WHILE e DO c END, rest'') } <|>
  do {
    (i, rest) ← parseIdentifier xs,
    (e, rest') ← firstExpect "::=" (parseAExp steps) rest,
    pure (i ::= e, rest') } <|>
  NoneE "Expecting a command"

with parseSequencedCommand : ℕ → parser com
| 0 := λ_, NoneE "Too many recursive calls"
| (succ steps) := λxs,
  have steps < succ steps, from lt_succ_self steps,
  do (c, rest) ← parseSimpleCommand steps xs,
  do {
    (c', rest') ← firstExpect ";;" (parseSequencedCommand steps) rest,
    pure (c ;; c', rest') } <|>
  pure (c, rest)

def bignumber := 1000

def parse (str) : optionE com :=
match parseSequencedCommand bignumber $ tokenize str with
| SomeE (c, []) := SomeE c
| SomeE (_, t :: _) := NoneE $ "Trailing tokens remaining: " ++ t
| NoneE err := NoneE err
end

def com_tos : com → string
| CSkip := "SKIP"
| (CAss x a) := x ++ "::=" ++ aexp_tos a
| (CSeq c₁ c₂) := com_tos c₁ ++ ";;" ++ com_tos c₂
| (CIf b c₁ c₂) :=
  "IF " ++ bexp_tos b ++
  " THEN " ++ com_tos c₁ ++
  " ELSE " ++ com_tos c₂ ++
  " FI"
| (CWhile b c) := "WHILE " ++ bexp_tos b ++ " DO " ++ com_tos c ++ " END"

instance com_repr : has_repr com := ⟨com_tos⟩

/-
Example eg1 : parse "
  TEST x = y + 1 + 2 - y * 6 + 3 THEN
    x ::= x * 1;;
    y ::= 0
  ELSE
    SKIP
  END "
=
  SomeE (
      TEST "x" = "y" + 1 + 2 - "y" * 6 + 3 THEN
        "x" ::= "x" * 1;;
        "y" ::= 0
      ELSE
        SKIP
      FI)%imp.
Proof. cbv. reflexivity. Qed.

Example eg2 : parse "
  SKIP;;
  z::=x*y*(x*x);;
  WHILE x=x DO
    TEST (z ≤ z*z) && ~(x = 2) THEN
      x ::= z;;
      y ::= z
    ELSE
      SKIP
    END;;
    SKIP
  END;;
  x::=z "
=
  SomeE (
      SKIP;;
      "z" ::= "x" * "y" * ("x" * "x");;
      WHILE "x" = "x" DO
        TEST ("z" ≤ "z" * "z") && ~("x" = 2) THEN
          "x" ::= "z";;
          "y" ::= "z"
        ELSE
          SKIP
        FI;;
        SKIP
      END;;
      "x" ::= "z")%imp.
Proof. cbv. reflexivity. Qed.
-/

#eval parse "
  TEST x = y + 1 + 2 - y * 6 + 3 THEN
    x ::= x * 1;;
    y ::= 0
  ELSE
    SKIP
  END
"

/-
TODO - notation for numbers is broke af
also, kind of seems like lean can't handle this?
-/
-- example : parse "
--   TEST x = y + 1 + 2 - y * 6 + 3 THEN
--     x ::= x * 1;;
--     y ::= 0
--   ELSE
--     SKIP
--   END
-- " = SomeE (
--   TEST BEq "x" ("y" + 1 + 2 - "y" * 6 + 3) THEN
--     "x" ::= "x" * 1;;
--     "y" ::= 0
--   ELSE
--     SKIP
--   FI
-- ) := begin

-- end

#eval parse "
  SKIP;;
  z::=x*y*(x*x);;
  WHILE x=x DO
    TEST (z ≤ z*z) && ¬(x = 2) THEN
      x ::= z;;
      y ::= z
    ELSE
      SKIP
    END;;
    SKIP
  END;;
  x ::= z
"

end impparser