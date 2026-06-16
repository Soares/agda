-- Tests for forced dot patterns in --postfix-methods copattern LHS.
--
-- Fix 1: .(expr) (CannotBeProjectionPattern) must not be misclassified as a
-- postfix copattern by splitOnDotProjs.  Before the fix, isDotProjPat matched
-- PossiblyProjectionPattern with '_', so .(leaf) was treated as a copattern
-- and rejected.
--
-- Regression introduced alongside the postfix-methods feature.

{-# OPTIONS --postfix-methods #-}
module PostfixMethodsDotPattern where

open import Agda.Builtin.Equality

data Foo : Set where
  bar : Foo
  baz : Foo

-- On the top-level LHS, a forced dot pattern .(ctor) must be accepted.
-- Previously .(bar) caused a scope error because isDotProjPat matched it
-- as a postfix copattern (ignoring PossiblyProjectionPattern flag).
f : (x y : Foo) → x ≡ y → Foo
f bar .(bar) refl = bar
f baz .(baz) refl = baz

-- Genuine postfix copatterns must still work (regression guard).
record Pair (A B : Set) : Set where
  field fst : A
        snd : B

open Pair

swap : {A B : Set} → Pair A B → Pair B A
swap p .fst = p .snd
swap p .snd = p .fst

-- Module-style copattern definition (mirrors LRBrak:Pr .Run = LRBrak).
record Container (A : Set) : Set where
  field tag : A

val : Container Foo
val .tag = bar
