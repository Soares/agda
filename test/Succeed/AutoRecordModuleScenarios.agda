-- B4: synonym usable in every binding context where it can appear.
-- Syntax reminder:
--   telescope / type position : (module A : Cat)   {module A : Cat}
--   clause LHS pattern        : (A with Cat module) {A with Cat module}

module AutoRecordModuleScenarios where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat  using (Nat; zero; suc)

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

-- Pi-domain / function type.
applyTwice : (module A : Magma) → A.Carrier → A.Carrier
applyTwice (A with Magma module) x = x A.∘ (x A.∘ x)

-- Lambda binder.  Synonym from λ-bound module parameter.
applyLambda : (m : Magma) → Magma.Carrier m → Magma.Carrier m
applyLambda = λ (module A : Magma) → λ x → x A.∘ x


-- Let binding in a clause body.
letBind : (module A : Magma) → Magma.Carrier A → Magma.Carrier A
letBind (A with Magma module) x =
  let y : A.Carrier
      y = x A.∘ x
  in y

-- Synonym in scope when branching via if/then/else.
-- NOTE: `with` abstraction on a plain parameter in the same clause as a
-- module-synonym annotation triggers WithOnFreeVariable, because the synonym
-- scoping mechanism wraps the whole clause in an implicit where-module, making
-- all outer parameters module-telescope variables (over which `with` may not
-- abstract).  Use `if/then/else` or a helper to work around this.
ifSynonym : Bool → (module A : Magma) → Magma.Carrier A → Magma.Carrier A → Magma.Carrier A
ifSynonym true  (A with Magma module) x _ = x A.∘ x
ifSynonym false (A with Magma module) _ y = y A.∘ y

-- Synonym usable inside a where-block reached by pattern matching.
ifWhere : Bool → (module A : Magma) → Magma.Carrier A → Magma.Carrier A → Magma.Carrier A
ifWhere true  (A with Magma module) x _ = combined
  where combined : A.Carrier
        combined = x A.∘ x
ifWhere false (A with Magma module) _ y = y

-- Hidden binder in type; named-implicit synonym in clause.
hiddenSynonym : {module A : Magma} → Magma.Carrier A → Magma.Carrier A
hiddenSynonym {A = A with Magma module} x = x A.∘ x

-- Section with module params.
module WithSectionParam (module A : Magma) where
  double : A.Carrier → A.Carrier
  double x = x A.∘ x

-- Grouped binder: two synonyms, same record type.
pairOp : (module A B : Magma) → Magma.Carrier A → Magma.Carrier B → Magma.Carrier B
pairOp (A with Magma module) (B with Magma module) _ y = y B.∘ y
