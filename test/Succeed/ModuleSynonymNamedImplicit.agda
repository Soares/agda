-- B9: named-implicit module-synonym patterns {B = B with Cat module}.
-- The synonym is generated when matching an implicit by name.

module ModuleSynonymNamedImplicit where

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

-- Signature uses classic implicits; clause body uses synonym via named-implicit pattern.
twice : {A : Magma} → Magma.Carrier A → Magma.Carrier A
twice {A = A with Magma module} x = x A.∘ x

-- Only one implicit annotated; the other is inferred.
combine : {A B : Magma} → Magma.Carrier A → Magma.Carrier B → Magma.Carrier B
combine {B = B with Magma module} _ y = y B.∘ y

-- Named-implicit synonym usable in a where block.
twiceWhere : {A : Magma} → Magma.Carrier A → Magma.Carrier A
twiceWhere {A = A with Magma module} x = result
  where
    result : Magma.Carrier A
    result = x A.∘ x
