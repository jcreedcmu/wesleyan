{-# OPTIONS --without-K #-}
module InternalCategoriesStrippedDown where

open import HoTT

-- The type of categories whose set of objects is X
record Cat (X : Set) : Set₁ where
  constructor cat
  field
    hom : X → X → Set
    _⋆_ : {x y z : X} → hom x y → hom y z → hom x z
    id : {x : X} → hom x x
    assoc : {x y z w : X} {f : hom x y} {g : hom y z} {h : hom z w}
      → ((f ⋆ g) ⋆ h) == (f ⋆ (g ⋆ h))

-- The Cayley category of a family of sets F. Objects are elements of
-- X, and a morphism x → y is any function F x → F y.
cay : (X : Set) (F : X → Set) → Cat X
cay X F = cat (λ x y → F x → F y) (λ f g → g ∘ f) (λ z → z) idp

-- The 'Cayley axiom': every category is Cayley. Contrast this with
-- the Yoneda lemma, which says that every category is the subcategory
-- of a Cayley category. We are thereby postulating into existence the
-- more exotic types that have the specified homs.
--
-- This (or something like this, with further restrictions on the size
-- of the categories involved --- consider maybe postulating this only
-- for finite categories?) smells like maybe it should be validated by
-- a presheaf model whose base category is a big aggregation somehow
-- (product? coproduct?) of all categories involved, or something like
-- that?
postulate
  cay-equiv : {X : Set} → is-equiv (cay X)
