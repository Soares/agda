-- B7: the `module` synonym marker in a data/record *definition* parameter
-- has no effect (synonyms are generated from the *signature* parameters).
-- Agda should warn and suggest annotating the signature instead.

module ModuleSynonymInDefParam where

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

-- Data: split signature + definition.
-- Signature has a plain param (synonym would come from here).
data Wrap (A : Magma) : Set₁

-- Definition uses `module` marker — ineffective here, warns.
data Wrap (module A : Magma) where
  wrap : Magma.Carrier A → Wrap A

-- Record: same pattern.
record Pair (A : Magma) : Set₁

record Pair (module A : Magma) where
  field fst snd : Magma.Carrier A
