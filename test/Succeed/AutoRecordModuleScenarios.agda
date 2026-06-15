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

-- `with`-abstraction alongside a module-synonym annotation.
-- The synonym scoping uses a let-binding rather than a where-module, so outer
-- function parameters remain ordinary variables (not module-free variables) and
-- `with` may abstract over them normally.
withSynonym : Bool → (module A : Magma) → Magma.Carrier A → Magma.Carrier A → Magma.Carrier A
withSynonym b (A with Magma module) x y with b
... | true  = x A.∘ x
... | false = y A.∘ y

-- Synonym in scope when branching via pattern matching (alternative to `with`).
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

-- Let-PATTERN binding: synonym available in the continuation body.
-- `let (B with Magma module) = m in body` must bring B.∘ into scope.
letPatSynonym : (m : Magma) → Magma.Carrier m → Magma.Carrier m
letPatSynonym m x =
  let (B with Magma module) = m
  in x B.∘ x

-- B8: optional `as Alias` alias in postfix synonym binder.
-- `(inst as M with Magma module)` binds variable `inst` but creates
-- module synonym `M` (so M.∘ is in scope, not inst.∘).
aliasedSynonym : (inst as M with Magma module) → M.Carrier → M.Carrier
aliasedSynonym (inst as M with Magma module) x = x M.∘ x
