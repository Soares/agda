-- Clause-level module synonyms (here via an `(A with module : T)` pattern)
-- do not leak from a named, public where module.
module AutoRecordModulesPrivateWhere where

open import Agda.Builtin.Nat

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

f : (module A : Magma) → A.Carrier → A.Carrier
f (A with module : Magma) x = twice
  module W where
    twice : Magma.Carrier A
    twice = x A.∘ x

leak : (module A : Magma) → A.Carrier → A.Carrier
leak A x = f.W.A.Carrier
