{-# OPTIONS --without-K --rewriting #-}
module FunctionalRelations where

open import HoTT hiding (Span ; S ; span=)

-- I don't really need pulls to tell me what morphisms are functional-in-one-direction;
-- A morphism #1 → X factoring through ⊤ should be necessary and sufficient information
-- to consider it trivial.

postulate
  # : Set → Set
  ι : {n : Set} → n → # n
  -- # is a functor:
  #F : {A B : Set} → (A → B) → # A → # B
  -- ι is a natural transformation:
  ιnat : {A B : Set} (f : A → B) → #F f ∘ ι == ι ∘ f

data 𝟚 : Set where -- walking binary relation
  dom cod : 𝟚

isTriv : {X : Set} (f : # ⊤ → X) → Set
isTriv {X} f = Σ X (λ x → (z : # ⊤) → f z == x)

isDir : {X : Set} (f : # 𝟚 → X) → Set
isDir f = isTriv (f ∘ (#F (λ { tt → dom })))

Mor : {X : Set} (x y : X) → Set
Mor {X} x y = Σ (# 𝟚 → X) (λ ρ → isDir ρ × (ρ (ι dom) == x) × (ρ (ι cod) == y))

Adj : {C D : Set} (F : C → D) (G : D → C) → Set
Adj {C} {D} F G = (c : C) (d : D) → Mor (F c) d ≃ Mor c (G d)

-- Each pull is a right adjoint to a push
-- if we think of the type of push (with respect to f : m → n) as
--       ĝ
--    #n → X         #m → #n → X
--    over      ↦        over
-- n ----→ X           m ----→ X
--     g                   gf

{- compare ../anon/2018-04-14.agda -}

R : {A B : Set} → (A → B) → Set
R {A} {B} g = Σ (# A → B) (λ f → f ∘ ι == g)

push : {m n X : Set} {f : m → n} {g : n → X} → R g → R (g ∘ f)
push {m} {n} {X} {f} {.(λ x → ĝ (ι x))} (ĝ , idp) = (ĝ ∘ #F f) , (ap (ĝ ∘_) (ιnat f))

isPull : {m n X : Set} {f : m → n} {g : n → X} → (putative : R (g ∘ f) → R g) → Set
isPull putative = Adj push putative

-- to prove adjoints are unique, somehow??
