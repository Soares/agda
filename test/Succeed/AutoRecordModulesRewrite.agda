-- B4 coverage: synonym available in `rewrite` position.

module AutoRecordModulesRewrite where

open import Agda.Builtin.Equality

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

-- Synonym in scope for the rewrite expression and the resulting goal.
rewriteTest : (A : Magma) (x y : Magma.Carrier A) → x ≡ y → Magma.Carrier A → Magma.Carrier A
rewriteTest (A with Magma module) x y eq z rewrite eq = z A.∘ z

-- Synonym in scope for a rewrite followed by a where clause.
rewriteWhere : (A : Magma) (x y : Magma.Carrier A) → x ≡ y → Magma.Carrier A
rewriteWhere (A with Magma module) x y eq rewrite eq = double
  where
    double : Magma.Carrier A
    double = y A.∘ y
