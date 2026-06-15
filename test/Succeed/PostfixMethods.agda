-- Tests for the --postfix-methods extension of postfix projections:
-- under the flag, `x .foo` resolves `foo` against the record module of x's
-- type (fields AND non-field "methods"), ignoring the ambient scope.
{-# OPTIONS --postfix-methods #-}
module PostfixMethods where

open import Agda.Builtin.Equality

postulate
  N : Set
  z : N
  s : N → N

data Tag : Set where fromMethod fromGlobal : Tag

record Box (A : Set) : Set where
  field
    unbox : A
  -- non-field members ("methods") of the record module:
  twice : (A → A) → A
  twice f = f (f unbox)

  same : A
  same = unbox

w : Box N
w = record { unbox = z }

-- Bare postfix field (record not opened, no qualifier):
field-bare : N
field-bare = w .unbox

-- Bare postfix method:
method-bare : N
method-bare = w .twice s

-- Qualified postfix method also works:
method-qual : N
method-qual = w .Box.twice s

-- Principal may be an arbitrary expression, keyed off its type:
mk : N → Box N
mk n = record { unbox = n }

compound : N
compound = (mk z) .twice s

-- Computation is by the record member:
field-computes : (w .unbox) ≡ z
field-computes = refl

method-computes : (w .same) ≡ z
method-computes = refl

compound-computes : ((mk z) .same) ≡ z
compound-computes = refl

-- A global `meth` is shadowed by the record's `meth` member: `r .meth`
-- resolves to the member, never the global.
record R : Set where
  field dummy : Tag
  meth : Tag
  meth = fromMethod

meth : R → Tag
meth _ = fromGlobal

r : R
r = record { dummy = fromMethod }

shadowing : (r .meth) ≡ fromMethod
shadowing = refl

-- Principal with implicit telescope: when the principal's inferred type has
-- a non-visible (implicit or instance) prefix, the implicit args are
-- introduced as metas.  The metas must be solved by coercing the result to
-- the expected type — the `coerce'` call in checkPostfixMemberApp is what
-- makes this work.
--
-- We use a record parameterised by two types so that the implicit arg
-- appears in the record parameters (not as a bare meta in the result type).
-- The method's return type is `A → B`, so when the expected type is `N → N`
-- the unifier solves `A = N` and `B = N` through the record parameters.
record Fun (A B : Set) : Set where
  field apply : A → B
  swap : B → A → B
  swap y x = apply x

postulate fun : {A B : Set} → Fun A B

implicit-principal-field : N → N
implicit-principal-field = fun .apply

implicit-principal-method : N → N → N
implicit-principal-method = fun .swap

-- Copattern definitions using postfix notation: `x .field = rhs` should work
-- as a copattern clause even when the record is not opened.
record Baz : Set2 where
  field qux : Set1

copat : Baz
copat .qux = Set
