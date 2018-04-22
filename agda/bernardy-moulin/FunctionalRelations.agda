{-# OPTIONS --without-K --rewriting #-}
module FunctionalRelations where

open import HoTT hiding (Span ; S ; span=)

-- I don't really need pulls to tell me what morphisms are functional-in-one-direction;
-- A morphism #1 → X factoring through ⊤ should be necessary and sufficient information
-- to consider it trivial.

postulate
  # : Set → Set
  ι : {n : Set} → n → # n
  #F : {A B : Set} → (A → B) → # A → # B


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
