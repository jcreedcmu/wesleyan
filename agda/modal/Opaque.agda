open import HoTT
open import Modes

-- This is like Opaque.agda, but we're not even thinking of the
-- translation as a translation per se, just a design pattern whereby
-- we simply show how to construct substructural propositions from
-- others.

data Post : Set where
  mult shft : Post

module Opaque where

record OpaqueModeTheory : Set₁ where
  constructor OMTh
  field
    Mode : Set
    Res : Mode → Set
    Opr : Post → Set
    Input : {π : Post} → Opr π → List Mode
    Output : {π : Post} → Opr π → Mode
    Reln : {π : Post} (ω : Opr π) → Mlist Res (Input ω) → Res (Output ω) → Set

module TurnCrank (OT : OpaqueModeTheory) where
  open OpaqueModeTheory OT

  data Prop : Mode → Set where
    C : {π : Post} (ω : Opr π) → Mlist Prop (Input ω) → Prop (Output ω)

  _⋆_ : {μs : Mode} → Prop μs → Res μs → Set
  _⋆s_ : {L : List Mode} → Mlist Prop L → Mlist Res L → Set

  C {mult} ω ps ⋆ α = Σ (Mlist Res (Input ω)) (λ βs → (ps ⋆s βs) × Reln ω βs α)
  C {shft} ω ps ⋆ α = Π (Mlist Res (Input ω)) (λ βs → (ps ⋆s βs) → Reln ω βs α)

  nil ⋆s nil = Unit
  (p :: ps) ⋆s (β :: βs) = (p ⋆ β) × (ps ⋆s βs)
