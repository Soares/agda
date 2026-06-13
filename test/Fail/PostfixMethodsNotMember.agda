-- Under --postfix-methods, `x .foo` is an error when `foo` is not a member
-- of x's record module -- even if a global `foo` is in scope.
{-# OPTIONS --postfix-methods #-}
module PostfixMethodsNotMember where

postulate
  N : Set
  z : N

record Box : Set where
  field unbox : N

w : Box
w = record { unbox = z }

-- `notThere` is not a member of Box's record module:
notThere : Box → N
notThere b = Box.unbox b

bad : N
bad = w .notThere
