open import HoTT
open import Modal

module TurnCrank where

module DoIt (MT : ModeTheory) where
  open ModeTheory MT

  data Prop : Signed Mode → Set
  data Prop where
    ↑ : {μ : Mode} → Prop (μ , s+) → Prop (μ , s-)
    ↓ : {μ : Mode} → Prop (μ , s-) → Prop (μ , s+)
    C : (ω : Opr) → Mlist Prop (Input ω) → Prop (Output ω)

  -- Interpretation Function
  _⋆_ : {μs : Signed Mode} → Prop μs → Res μs → Set
  _⋆s_ : {L : List (Signed Mode)} → Mlist Prop L → Mlist Res L → Set

  ↑ p ⋆ φ = (α : Res _) → p ⋆ α → ▹ _ α φ
  ↓ n ⋆ α = (φ : Res _) → n ⋆ φ → ▹ _ α φ
  C ω ps ⋆ α = Σ (Mlist Res (Input ω)) (λ βs → Reln ω βs α × (ps ⋆s βs))

  nil ⋆s nil = Unit
  (p :: ps) ⋆s (β :: βs) = (p ⋆ β) × (ps ⋆s βs)

TurnCrank : (MT : ModeTheory) → ProofTheory MT
TurnCrank MT = record { Prop = Prop ; _⋆_ = _⋆_ } where open DoIt MT
