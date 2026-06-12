-- A wrong pattern ascription is a type error.
module PatternAscriptionMismatch where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

bad : Nat → Nat
bad (b : Bool) = 0
