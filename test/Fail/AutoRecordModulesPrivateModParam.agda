-- Record module synonyms for module parameters are private:
-- the parameters are not part of the module's public interface.
{-# OPTIONS --auto-record-modules #-}
module AutoRecordModulesPrivateModParam where

open import Agda.Builtin.Nat

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

module WithParam (X : Magma) where
  double : X.Carrier → X.Carrier
  double x = x X.∘ x

M : Magma
M = record { Carrier = Nat ; _∘_ = _+_ }

leak : Set
leak = WithParam.X.Carrier M
