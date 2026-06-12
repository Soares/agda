-- Clause-level module synonyms (here for an ascribed pattern variable)
-- do not leak from a named, public where module.
{-# OPTIONS --auto-record-modules #-}
module AutoRecordModulesPrivateWhere where

open import Agda.Builtin.Nat

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

f : (A : Magma) → A.Carrier → A.Carrier
f (A : Magma) x = twice
  module W where
    twice : Magma.Carrier A
    twice = x A.∘ x

leak : (A : Magma) → A.Carrier → A.Carrier
leak A x = f.W.A.Carrier
