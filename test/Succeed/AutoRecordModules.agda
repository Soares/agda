module AutoRecordModules where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

record Magma : Set₁ where
  field
    Carrier : Set
    _∘_     : Carrier → Carrier → Carrier

-- A @module@-marked definition of record type gets a module synonym.
module M : Magma
M = record { Carrier = Nat ; _∘_ = _+_ }

five : M.Carrier
five = 2 M.∘ 3

-- An indexed family of records: the synonym is parameterized,
-- as if defined by  module F (b : Bool) = Magma (F b).
module F : Bool → Magma
F true  = M
F false = M

six : F.Carrier true
six = F._∘_ true 4 2

-- Implicit domains.
module G : {b : Bool} → Magma
G {b} = F b

seven : G.Carrier {true}
seven = G._∘_ {true} 3 4

-- Unnamed domains get invented binder names.
module H : Bool → Magma
H _ = M

eight : H.Carrier true
eight = H._∘_ true 4 4

-- Postulates get a synonym, too.
postulate
  module P : Magma

p-test : P.Carrier → P.Carrier
p-test x = x P.∘ x

-- Parameterized records: the parameters are taken from the target.
record Pointed (A : Set) : Set where
  field point : A

module Q : Pointed Nat
Q = record { point = 0 }

zero' : Nat
zero' = Q.point

-- Using the synonym already between signature and definition
-- (one mutual block).
module K : Magma
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

module W : WithDefs
W = record { A = Nat }

idTwice : W.Twice
idTwice x = x

-- Operator-named definitions get module synonyms too (record modules
-- named _×_ are precedent for operator-named modules).
module _⊗_ : Magma → Magma → Magma
x ⊗ y = x

twelve : _⊗_.Carrier M M
twelve = _⊗_._∘_ M M 5 7

-- An infix/mixfix operator in the *target* is recognized as the record
-- head: the target  A [hom] B  re-parses to the operator _[hom]_, so
-- the synonym  module homM = _[hom]_ (homM)  is generated (found
-- dogfooding in Brak's elim[W0] : ... → 𝕃:W0.Motive [P]> R.Motive).
record _[hom]_ (module A B : Magma) : Set where
  field
    map : A.Carrier → B.Carrier

module homM : M [hom] M
homM = record { map = λ x → x }

thirteen : M.Carrier → M.Carrier
thirteen = homM.map

-- A @module@-marked binder with an unrecognized (irrelevant) domain
-- form warns instead of failing silently; see the .warn file.
module viaIrr : .Magma → Magma
viaIrr _ = M

-- Module parameters of record type get a synonym inside the module.
module WithParam (module X : Magma) where
  double : X.Carrier → X.Carrier
  double x = x X.∘ x

-- Instantiating the parameterized module uses the synonym's copies.
fourteen : Nat
fourteen = WithParam.double M 7

-- Parameterized module parameter with a function type.
module FamParam (module Y : Bool → Magma) where
  use : (b : Bool) → Y.Carrier b → Y.Carrier b
  use b y = Y._∘_ b y y

-- Typed lambda binders get a let-scoped synonym.
lamTest : Magma → Nat → Nat
lamTest = λ (module Z : Magma) n → n + 1

lamTest2 : (X : Magma) → Magma.Carrier X → Magma.Carrier X
lamTest2 = λ (module X : Magma) x → x X.∘ x

-- Typed let binders get a synonym for subsequent bindings and the body.
letTest : Nat
letTest =
  let module L : Magma
      L = M
  in 3 L.∘ 4

-- Type-ascribed pattern variables.  A plain checked ascription (no
-- @module@, so no synonym):
ann1 : Nat → Nat
ann1 (n : Nat) = suc n

-- The ascription fills in a hole in the signature by unification.
ann2 : _ → Bool
ann2 (n : Nat) = true

-- Record-headed @module@-marked ascriptions give clause-scoped synonyms.
annSyn : (X : Magma) → Magma.Carrier X → Magma.Carrier X
annSyn (module A : Magma) x = x A.∘ x

-- Multiple variables in one ascription atom.
annTwo : Magma → Magma → Nat
annTwo (module A B : Magma) = 0

-- The synonym is in scope in with-expressions
-- (via the implicit where module).
annWith : (X : Magma) → Magma.Carrier X → Nat
annWith (module A : Magma) x with x A.∘ x
... | _ = 2

-- ... and in where blocks.
annWhere : (X : Magma) → Magma.Carrier X → Magma.Carrier X
annWhere (module A : Magma) x = twice
  where
    twice : Magma.Carrier A
    twice = x A.∘ x

-- Postfix copattern clauses with ascriptions.
record Pair : Set₁ where
  field
    fst snd : Magma

mkPair : Magma → Pair
mkPair (module A : Magma) .Pair.fst = A
mkPair (module A : Magma) .Pair.snd = record
  { Carrier = A.Carrier ; _∘_ = A._∘_ }

-- Unnamed instance and hidden function-space domains (their hiding
-- lives in a wrapper expression, not the ArgInfo; issue found
-- dogfooding in WildBracket's Shim.agda).
record HasMagma : Set₁ where
  field theMagma : Magma

module viaInst : {{HasMagma}} → Magma
viaInst {{h}} = HasMagma.theMagma h

useViaInst : {{h : HasMagma}} → viaInst.Carrier → viaInst.Carrier
useViaInst x = x viaInst.∘ x

module viaHid : {Bool} → Magma
viaHid = M

useViaHid : viaHid.Carrier {true} → Nat
useViaHid _ = 0

-- @module@-marked binders in using statements.
useUsing : (X : Magma) → Magma.Carrier X → Magma.Carrier X
useUsing X x using (module A : Magma) ← X = x A.∘ x

useUsingWhere : (X : Magma) → Magma.Carrier X → Magma.Carrier X
useUsingWhere X x using (module A : Magma) ← X = twice
  where
    twice : Magma.Carrier A
    twice = x A.∘ x

-- Pi-bound variables of record type get a synonym for the rest of the
-- telescope and the codomain (used heavily in dependent signatures).
piSyn : ∀ (module A : Magma) {q : A.Carrier} → A.Carrier → A.Carrier
piSyn (module A : Magma) x = x A.∘ x

-- Record parameters of record type get a synonym inside the record
-- module: in field types, in the constructor type, and in non-field
-- definitions (found dogfooding in WildBracket's Cat.agda).
record MagmaHom (module A B : Magma) : Set where
  field
    map  : A.Carrier → B.Carrier
    resp : A.Carrier → B.Carrier

  mapTwice : A.Carrier → B.Carrier
  mapTwice a = map (a A.∘ a) B.∘ resp a

idHom : (A : Magma) → MagmaHom A A
idHom (module A : Magma) = record { map = λ a → a ; resp = λ a → a A.∘ a }

-- The synonym also works when the record definition is separate from
-- its signature, including renamed parameters and omitted hidden ones.
record SepHom {module A : Magma} (module B : Magma) : Set
record SepHom Y where
  field sep : Y.Carrier

-- Hidden parameters mentioned in the definition align as well.
record SepHom2 {module A : Magma} (module B : Magma) : Set
record SepHom2 {X} Y where
  field sep2 : X.Carrier → Y.Carrier

-- Record-typed @module@-marked fields get a module synonym after the
-- field: in later field types, in non-field definitions in the record
-- body, and (public, like the field) from outside the record module.
record TwoMagmas : Set₁ where
  field
    module first  : Magma
    module second : Magma
    embed         : first.Carrier → second.Carrier

  back : first.Carrier → second.Carrier
  back x = embed (x first.∘ x)

mkTwo : TwoMagmas
mkTwo = record { first = M ; second = M ; embed = λ x → x }

useFieldSyn :
  (T : TwoMagmas) → TwoMagmas.first.Carrier T → TwoMagmas.second.Carrier T
useFieldSyn T = TwoMagmas.back T

-- Opening the record module applied to a value also brings the field
-- synonyms into scope.
module UseTwo (T : TwoMagmas) where
  open TwoMagmas T
  go : first.Carrier → second.Carrier
  go x = embed (x first.∘ x)

-- A field whose type mentions an earlier field through its synonym
-- (found dogfooding in WildBracket's Spec.agda).
record SpecLike : Set₁ where
  field
    module Mg : Magma
    module pt : Pointed Mg.Carrier
    out       : Mg.Carrier

  shifted : Mg.Carrier
  shifted = pt.point Mg.∘ out

mkSpecLike : SpecLike
mkSpecLike = record { Mg = M ; pt = Q ; out = 3 }

specOut : (S : SpecLike) → SpecLike.Mg.Carrier S
specOut = SpecLike.shifted

-- An irrelevant (or erased) @module@-marked field cannot be used in the
-- generated module application, so no synonym is generated; see the
-- .warn file.
record IrrField : Set₁ where
  field
    module .irrM : Magma

-- Data parameters of record type get a synonym: in the rest of the
-- data telescope and target type, and in the constructor types (found
-- dogfooding in WildBracket's Chain.agda).
data Walk (module A : Magma) (a : A.Carrier) : Set where
  stop : Walk A a
  step : A.Carrier → Walk A a → Walk A a

walkTwo : (module A : Magma) (a : A.Carrier) → Walk A a
walkTwo (module A : Magma) a = step (a A.∘ a) stop

-- The synonym is in scope in the indices and works with a separate
-- signature and renamed parameters.
data SepWalk (module A : Magma) : A.Carrier → Set
data SepWalk B where
  sep : (b : B.Carrier) → SepWalk B b

-- Hidden @module@-marked ascriptions give clause-scoped synonyms too
-- (dogfooding blocker: f {S1 : Spec} ... in WildBracket).
hidSyn : ∀ {A : Magma} → Magma.Carrier A → Magma.Carrier A
hidSyn {module A : Magma} x = x A.∘ x
