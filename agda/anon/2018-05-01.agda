{-# OPTIONS --without-K #-}
module 2018-05-01 where

open import HoTT

data obj : Set where
  oα oβ oγ : obj

data homSpec : obj → obj → Set where
  idh : (ω : obj) → homSpec ω ω
  p1 : homSpec oα oγ
  p2 : homSpec oβ oγ

postulate
  tp : obj → Set

α β γ : Set
α = tp oα
β = tp oβ
γ = tp oγ

postulate
  proj1 : α → γ
  proj2 : β → γ

realize : {ω1 ω2 : obj} → homSpec ω1 ω2 → tp ω1 → tp ω2
realize (idh ω) = λ z → z
realize p1 = proj1
realize p2 = proj2

postulate
  allTheHoms : {ω1 ω2 : obj} → is-equiv (realize {ω1} {ω2})

module spanToType (A B C : Set) (f : C → A) (g : C → B) where
  -- We take the pushout of
  -- C × (α + β) → (C x γ) (using proj1, proj2)
  -- and
  -- C × (α + β) → (A × α) + (B × β) (using f, g)
  -- to get a single type that represents the span.

  data branch : Set where
    branch1 : A → α → branch
    branch2 : B → β → branch

  pomap1 : C × α ⊔ β → C × γ
  pomap1 (c , inl x) = c , proj1 x
  pomap1 (c , inr x) = c , proj2 x

  pomap2 : C × α ⊔ β → branch
  pomap2 (c , inl x) = branch1 (f c) x
  pomap2 (c , inr x) = branch2 (g c) x

  go : Set
  go = Pushout (span (C × γ) branch (C × (α ⊔ β)) pomap1 pomap2)

  go2 : Set
  go2 = Pushout (span (γ → C × γ) (γ → branch) (γ → C × (α ⊔ β))
                (λ f e → pomap1 (f e)) (λ f e → pomap2 (f e)))

  intro : (c : C) → (γ → go)
  intro c g = left (c , g)

  -- Oh, but I shouldn't expect to prove this, it's like proving
  -- (A → (B + C)) → ((A → B) + (A → C))
  -- ...although, if γ is a tiny object in the sense of
  -- https://ncatlab.org/nlab/show/tiny+object
  -- then it would go through?
  elim : (γ → go) → go2
  elim gg = {!!}

  -- Let's imagine we have a polymorphic function
  module Parametricity (h : (X : Set) → X → X) where
    reln : (c : C) → f (h C c) == h A (f c)
    reln = {!!}

    blah : (c : C) → Set
    blah c = {!h (γ → go) (intro c)!}
