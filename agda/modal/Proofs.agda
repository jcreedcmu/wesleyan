open import HoTT
open import Modes

module Proofs where

-- A theory of what goes on `upstairs'
record ProofTheory (MT : ModeTheory) : Set₁ where
  open ModeTheory MT
  field
    -- A set of props
    Prop : Signed Mode → Set
    -- with an interpretation function
    _⋆_ : {μs : Signed Mode} → Prop μs → Res μs → Set

module TurnCrank (MT : ModeTheory) where
  open ModeTheory MT

  data Prop : Signed Mode → Set where
    ↑ : {μ : Mode} → Prop (μ , s+) → Prop (μ , s-)
    ↓ : {μ : Mode} → Prop (μ , s-) → Prop (μ , s+)
    C : (ω : Opr) → Mlist Prop (Input ω) → Prop (Output ω)

  -- Interpretation Function
  _⋆_ : {μs : Signed Mode} → Prop μs → Res μs → Set
  _⋆s_ : {L : List (Signed Mode)} → Mlist Prop L → Mlist Res L → Set

  ↑ p ⋆ φ = (α : Res _) → p ⋆ α → ▹ _ α φ
  ↓ n ⋆ α = (φ : Res _) → n ⋆ φ → ▹ _ α φ
  C ω ps ⋆ α = Σ (Mlist Res (Input ω)) (λ βs → (ps ⋆s βs) × Reln ω βs α)

  nil ⋆s nil = Unit
  (p :: ps) ⋆s (β :: βs) = (p ⋆ β) × (ps ⋆s βs)

  pft : ProofTheory MT
  pft = record { Prop = Prop ; _⋆_ = _⋆_ }
