{-# OPTIONS --without-K #-}
module Exercise3 where

open import HoTT hiding (_≤_ ; S)
open import Relational

pullf : {B C : Set} → B ⊔ (B ⊔ C) → (B ⊔ C)
pullf = cpf inl idn

cpf-lem : {B C X : Set} (g : B → X) (h : C → X) → cpf g (cpf g h) == cpf g h ∘ (cpf inl idn)
cpf-lem {B} {C} g h = cpf-eq (cpf g h)

-- join of two relations over overlapping support
join : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h)) → fib (cpf g h)
join {g = g} {h} R S = pull pullf (transport fib (cpf-lem g h) (copair R S))

{- A preview of the theorem we prove at the bottom is:

jointriv : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → push inl (join R S) == R

The square we'll want to apply the beck-chevalley condition to is

                cart
     B ⊔ C → X --------> B ⊔ (B ⊔ C) → X
          | _|           |
   opcart |              | opcart
          |              |
          v              v
       B → X ---------> B ⊔ B → X
                cart

so the assignment to the arguments of the postulate is
f := cpf g h, plus the b1, k1, b2, k2 below:
-}

module _ {B C : Set} where
  b1 : B ⊔ (B ⊔ C) → (B ⊔ C)
  b1 = pullf
  k1 : B ⊔ B → B ⊔ (B ⊔ C)
  k1 = cpf inl (inr ∘ inl)
  b2 : B → B ⊔ C
  b2 = inl
  k2 : B ⊔ B → B
  k2 = cpf idn idn

  -- The b's and k's commute appropriately:
  b1k1~b2k2 : (x : B ⊔ B) → b1 (k1 x) == b2 (k2 x)
  b1k1~b2k2 (inl _) = idp
  b1k1~b2k2 (inr _) = idp

jointriv2 : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → pull (k2 {C = C})
      (transport (λ z → fib (cpf g h ∘ z)) (λ= b1k1~b2k2)
       (push k1 (transport fib (cpf-lem g h) (copair R S))))
      == R
jointriv2  = {!!}
{- 2. We transform the goal with beck-chevalley... -}

jointriv1 : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → push inl (pull {f = cpf g h} pullf (transport fib (cpf-lem g h) (copair R S))) == R
jointriv1 {B} {C} g h R S p =
  beck-chevalley {k1 = k1} (λ= b1k1~b2k2) (transport fib (cpf-lem g h) (copair R S))
  ∙ jointriv2 g h R S p
{- 1. We expand the definition of join... -}

jointriv : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → push inl (join R S) == R
jointriv g h R S p = jointriv1 g h R S p
{- 0. This part of the story can be read backwards... -}
