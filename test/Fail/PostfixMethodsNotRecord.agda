-- Under --postfix-methods, `x .foo` requires x to have a record type.
{-# OPTIONS --postfix-methods #-}
module PostfixMethodsNotRecord where

postulate
  N : Set
  z : N

bad : N
bad = z .foo
