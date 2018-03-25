open import HoTT
open import Modal

-- The goal of this file is to forget that the positive and negative
-- aspects of a mode are special, and think of them as merely two
-- different modes. By doing this we can see multiplicatives
-- and shifts as very similar kinds of connectives.

-- The two Postures, multiplicative and shift-like
data Post : Set where
  mult : Post
  shft : Post

module Opaque where

record OpaqueModeTheory : Set₁ where
  field
    Mode : Set
    Res : Mode → Set
    Opr : Post → Set
    Input : {π : Post} → Opr π → List Mode
    Output : {π : Post} → Opr π → Mode
    Reln : {π : Post} (ω : Opr π) → Mlist Res (Input ω) → Res (Output ω) → Set

record ProofTheory (MT : OpaqueModeTheory) : Set₁ where
  open OpaqueModeTheory MT
  field
    Prop : Mode → Set
    _⋆_ : {μs : Mode} → Prop μs → Res μs → Set

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

  pft : ProofTheory OT
  pft = record { Prop = Prop ; _⋆_ = _⋆_ }
