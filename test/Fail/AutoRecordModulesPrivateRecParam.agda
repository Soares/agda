-- Record module synonyms for record parameters are private:
-- they are not part of the record module's public interface.
{-# OPTIONS --auto-record-modules #-}
module AutoRecordModulesPrivateRecParam where

open import Agda.Builtin.Nat

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

record Hom (A B : Magma) : Set where
  field map : A.Carrier → B.Carrier

leak : (A B : Magma) → Hom A B → Set
leak A B h = Hom.A.Carrier
