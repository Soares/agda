-- Regression: {x = y = z} is now syntactically reachable (side-effect of
-- allowing the module-ascription form {x = y with T module} on the RHS of a
-- named argument).  It must be rejected with a helpful error.

module ModuleSynonymNestedNamedArgFail where

record Magma : Set₁ where
  field Carrier : Set

bad : {A B : Magma} → Set
bad {A = x = y} = Magma.Carrier y
