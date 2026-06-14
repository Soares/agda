-- Same rejection applies under --cubical: {i = j = i0} should not be a
-- back-door into nested face patterns in named-implicit position.

{-# OPTIONS --cubical #-}
module ModuleSynonymNestedNamedArgCubicalFail where

open import Agda.Primitive.Cubical using (I; i0)

bad : {i j : I} → I
bad {i = j = i0} = j
