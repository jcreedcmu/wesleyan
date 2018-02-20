{-# OPTIONS --without-K --rewriting #-}
module BaseCategory where

-- Trying to sketch out what I think is a category ℂ for which I want
-- to study the behavior of Set^ℂ.

open import HoTT

-- Forgot the stdlib name of this
data Maybe (A : Set) : Set where
  none : Maybe A
  some : A → Maybe A

-- A sigma of a function and its domain and codomain.
-- These are the objects of ℂ.
record Arrow : Set₁ where
  constructor arrow
  field
    src : Set
    dst : Set
    f : src → dst
open Arrow

-- The fiber over an element of the base set of such an arrow
fib : (A : Arrow) (ad : A .dst) → Set
fib A ad = Σ (A .src) (λ as → A .f as == ad)

module Take1 where
  -- Auxiliary type used to define morphisms
  data Out (A B : Arrow) (ad : A .dst) : Set where
    -- "some"
    Os : (bd : B .dst) (π : fib B bd → fib A ad) → Out A B ad
    -- "none"
    On : (π : fib A ad) → Out A B ad

  -- The morphisms of the category ℂ.
  Mor : (A B : Arrow) → Set
  Mor A B = (ad : A .dst) → Out A B ad

  -- Composition
  compose : {A B C : Arrow} → Mor A B → Mor B C → Mor A C
  compose {A} {B} {C} f g ad = lemma (f ad) where
    lemma : Out A B ad → Out A C ad
    lemma (Os bd π) = lemma2 (g bd) where
      lemma2 : Out B C bd → Out A C ad
      lemma2 (Os bd' π') = Os bd' (π ∘ π')
      lemma2 (On π') = On (π π')
    lemma (On π) = On π

  -- Identities
  ident : (A : Arrow) → Mor A A
  ident A ad = Os ad (idf _)

module Take2 where

  -- Auxiliary types used to define morphisms
  Out : (B : Arrow) (mbd : Maybe (B .dst)) → Set
  Out B none = ⊤
  Out B (some bd) = fib B bd

  Aux : (A B : Arrow) (ad : A .dst) → Set
  Aux A B ad = Σ (Maybe (B .dst)) (λ mbd → Out B mbd → fib A ad)

  -- The morphisms of the category ℂ.
  Mor : (A B : Arrow) → Set
  Mor A B = (ad : A .dst) → Aux A B ad

  -- Composition
  compose : {A B C : Arrow} → Mor A B → Mor B C → Mor A C
  compose {A} {B} {C} f g ad = lemma (f ad) where
    lemma : Aux A B ad → Aux A C ad
    lemma (none , h) = none , h
    lemma (some bd , h) = lemma2 (g bd) where
      lemma2 : Aux B C bd → Aux A C ad
      lemma2 (q , k) = q , h ∘ k

  -- Identities
  ident : (A : Arrow) → Mor A A
  ident A ad = (some ad) , idf _
