open import HoTT
open import Modes

module Proofs2 where

module TurnCrank (MT : ModeTheory) where
  open ModeTheory MT

  Prop : Signed Mode → Set₁
  Prop μs = Res μs → Set

  com : ∀ {ℓ ℓ'} {A : Set ℓ'} {F : A → Set ℓ} {ms : List A}
    → Mlist (λ μ → F μ → Set) ms → Mlist F ms → Set
  com nil nil = Unit
  com (p :: ps) (β :: βs) = p β × (com ps βs)

  -- zip : ∀ {ℓ ℓ'} {A : Set ℓ'} {F G : A → Set ℓ} {ms : List A}
  --   → Mlist F ms → Mlist G ms → Mlist (λ a → F a × G a) ms
  -- zip nil nil = nil
  -- zip (p :: ps) (β :: βs) = (p , β) :: (zip ps βs)

  -- mmap : ∀ {ℓ ℓ'} {A : Set ℓ'} {F G : A → Set ℓ} {ms : List A}
  --   → ({a : A} → F a → G a)
  --   → Mlist F ms → Mlist G ms
  -- mmap f nil = nil
  -- mmap f (p :: ps) = f p :: (mmap f ps)

  ↑ : {μ : Mode} → Prop (μ , s+) → Prop (μ , s-)
  ↑ p φ = (α : Res _) → p α → ▹ _ α φ

  ↓ : {μ : Mode} → Prop (μ , s-) → Prop (μ , s+)
  ↓ p α = (φ : Res _) → p φ → ▹ _ α φ

  C : (ω : Opr) → Mlist Prop (Input ω) → Prop (Output ω)
  C ω ps α = Σ (Mlist Res (Input ω)) (λ βs → com ps βs × Reln ω βs α)
