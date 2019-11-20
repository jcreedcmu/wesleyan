{-# OPTIONS --without-K --rewriting #-}
module 2019-11-20 where

open import HoTT hiding (S ; _+_)

postulate
  I : Set
  i0 ih i1 : I
  ↑ ↓ : I → I
  ↑0-rewrite : ↑ i0 ↦ ih
  ↓1-rewrite : ↓ i1 ↦ ih
  ↑1-rewrite : ↑ i1 ↦ i1
  ↓0-rewrite : ↓ i0 ↦ i0
{-# REWRITE ↑0-rewrite ↓1-rewrite ↑1-rewrite ↓0-rewrite #-}

record Pack (A : Set) : Set where
  constructor pack
  field
    ℓ r : I → A
    p : ℓ i1 == r i0

decompose : {A : Set} (f : I → A) → Pack A
decompose f = pack (f ∘ ↓) (f ∘ ↑) idp

postulate
 decompose-is-equiv : {A : Set} → is-equiv (decompose {A})

compose : {A : Set} → Pack A → (I → A)
compose = decompose-is-equiv .is-equiv.g
