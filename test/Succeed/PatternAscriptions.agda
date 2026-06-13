-- Type-ascribed pattern variables in clause left hand sides.
module PatternAscriptions where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

-- A plain checked ascription.
f : Nat → Nat
f (n : Nat) = suc n

-- The ascription fills in a hole in the signature by unification.
g : _ → Bool
g (n : Nat) = true

-- Multiple variables in one ascription atom.
plus : Nat → Nat → Nat
plus (m n : Nat) = m + n

-- Ascriptions in later argument positions, mixed with other patterns.
h : Bool → Nat → Nat
h true  (n : Nat) = n
h false (n : Nat) = suc n

-- Ascriptions in with-clauses and where blocks.
k : Nat → Nat
k (n : Nat) with n
... | zero  = zero
... | suc m = helper
  where
    helper : Nat
    helper = m

-- Postfix copattern clauses.
record Pair : Set where
  field
    fst snd : Nat

mkPair : Nat → Pair
mkPair (n : Nat) .Pair.fst = n
mkPair (n : Nat) .Pair.snd = suc n

-- Bare-pattern ascriptions: an ascribed parenthesized pattern matches.
constrMatch : Nat → Nat
constrMatch ((suc n) : Nat) = n
constrMatch ((zero)  : Nat) = zero

-- As-binders in ascriptions.
asMatch : Nat → Nat
asMatch (m@(suc n) : Nat) = m + n
asMatch (z@zero    : Nat) = z

-- Ascribed binders in using statements.
viaUsing : Nat → Nat
viaUsing k using (n : Nat) ← suc k = n + n

-- Hidden and instance arguments can also be type-ascribed binders.
hidAsc : {n : Nat} → Nat
hidAsc {n : Nat} = n

instAsc : ⦃ b : Bool ⦄ → Bool
instAsc {{b : Bool}} = b

-- Several names in one pair of braces give one hidden argument each.
twoHid : {n m : Nat} → Nat
twoHid {n m : Nat} = n + m

-- As-binders inside hidden ascriptions.
hidAs : {n : Nat} → Nat
hidAs {n@m : Nat} = n + m
