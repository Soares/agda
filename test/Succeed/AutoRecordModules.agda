{-# OPTIONS --auto-record-modules #-}

module AutoRecordModules where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

-- A direct definition of record type gets a module synonym.
M : Magma
M = record { Carrier = Nat ; _∘_ = _+_ }

five : M.Carrier
five = 2 M.∘ 3

-- An indexed family of records: the synonym is parameterized,
-- as if defined by  module F (b : Bool) = Magma (F b).
F : Bool → Magma
F true  = M
F false = M

six : F.Carrier true
six = F._∘_ true 4 2

-- Implicit domains.
G : {b : Bool} → Magma
G {b} = F b

seven : G.Carrier {true}
seven = G._∘_ {true} 3 4

-- Unnamed domains get invented binder names.
H : Bool → Magma
H _ = M

eight : H.Carrier true
eight = H._∘_ true 4 4

-- Postulates get a synonym, too.
postulate
  P : Magma

p-test : P.Carrier → P.Carrier
p-test x = x P.∘ x

-- Parameterized records: the parameters are taken from the target.
record Pointed (A : Set) : Set where
  field point : A

Q : Pointed Nat
Q = record { point = 0 }

zero' : Nat
zero' = Q.point

-- Using the synonym already between signature and definition
-- (one mutual block).
K : Magma
ten : K.Carrier
K = M
ten = 10

-- `open` on the generated module.
open M renaming (_∘_ to _⊕_)

nine : Nat
nine = 4 ⊕ 5

-- Non-field definitions in the record module are copied as well.
record WithDefs : Set₁ where
  field A : Set
  Twice : Set
  Twice = A → A

W : WithDefs
W = record { A = Nat }

idTwice : W.Twice
idTwice x = x

-- Operator-named definitions get module synonyms too (record modules
-- named _×_ are precedent for operator-named modules).
_⊗_ : Magma → Magma → Magma
x ⊗ y = x

twelve : _⊗_.Carrier M M
twelve = _⊗_._∘_ M M 5 7

-- An unrecognized (irrelevant) domain form warns instead of failing
-- silently; see the .warn file.
viaIrr : .Magma → Magma
viaIrr _ = M

-- Module parameters of record type get a synonym inside the module.
module WithParam (X : Magma) where
  double : X.Carrier → X.Carrier
  double x = x X.∘ x

-- Instantiating the parameterized module uses the synonym's copies.
fourteen : Nat
fourteen = WithParam.double M 7

-- Parameterized module parameter with a function type.
module FamParam (Y : Bool → Magma) where
  use : (b : Bool) → Y.Carrier b → Y.Carrier b
  use b y = Y._∘_ b y y

-- Typed lambda binders get a let-scoped synonym.
lamTest : Magma → Nat → Nat
lamTest = λ (Z : Magma) n → n + 1

lamTest2 : (X : Magma) → Magma.Carrier X → Magma.Carrier X
lamTest2 = λ (X : Magma) x → x X.∘ x

-- Typed let binders get a synonym for subsequent bindings and the body.
letTest : Nat
letTest =
  let L : Magma
      L = M
  in 3 L.∘ 4

-- Type-ascribed pattern variables.  A plain checked ascription:
ann1 : Nat → Nat
ann1 (n : Nat) = suc n

-- The ascription fills in a hole in the signature by unification.
ann2 : _ → Bool
ann2 (n : Nat) = true

-- Record-headed ascriptions give clause-scoped module synonyms.
annSyn : (X : Magma) → Magma.Carrier X → Magma.Carrier X
annSyn (A : Magma) x = x A.∘ x

-- Multiple variables in one ascription atom.
annTwo : Magma → Magma → Nat
annTwo (A B : Magma) = 0

-- The synonym is in scope in with-expressions
-- (via the implicit where module).
annWith : (X : Magma) → Magma.Carrier X → Nat
annWith (A : Magma) x with x A.∘ x
... | _ = 2

-- ... and in where blocks.
annWhere : (X : Magma) → Magma.Carrier X → Magma.Carrier X
annWhere (A : Magma) x = twice
  where
    twice : Magma.Carrier A
    twice = x A.∘ x

-- Postfix copattern clauses with ascriptions.
record Pair : Set₁ where
  field
    fst snd : Magma

mkPair : Magma → Pair
mkPair (A : Magma) .Pair.fst = A
mkPair (A : Magma) .Pair.snd = record
  { Carrier = A.Carrier ; _∘_ = A._∘_ }

-- Unnamed instance and hidden function-space domains (their hiding
-- lives in a wrapper expression, not the ArgInfo; issue found
-- dogfooding in WildBracket's Shim.agda).
record HasMagma : Set₁ where
  field theMagma : Magma

viaInst : {{HasMagma}} → Magma
viaInst {{h}} = HasMagma.theMagma h

useViaInst : {{h : HasMagma}} → viaInst.Carrier → viaInst.Carrier
useViaInst x = x viaInst.∘ x

viaHid : {Bool} → Magma
viaHid = M

useViaHid : viaHid.Carrier {true} → Nat
useViaHid _ = 0

-- Ascribed binders in using statements.
useUsing : (X : Magma) → Magma.Carrier X → Magma.Carrier X
useUsing X x using (A : Magma) ← X = x A.∘ x

useUsingWhere : (X : Magma) → Magma.Carrier X → Magma.Carrier X
useUsingWhere X x using (A : Magma) ← X = twice
  where
    twice : Magma.Carrier A
    twice = x A.∘ x
