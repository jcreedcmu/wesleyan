open import HoTT
-- This is a more standalone version of Opaque.agda, but we're not
-- even thinking of the translation as a translation per se, just a
-- design pattern whereby we simply show how to construct
-- substructural propositions from others.
module Opaque2 where

data Mlist {ℓ ℓ'} {U : Set ℓ} (El : U → Set ℓ') : List U → Set (lmax ℓ ℓ') where
  nil : Mlist El nil
  _::_ : {A : U} {L : List U} → El A → Mlist El L → Mlist El (A :: L)

record ModeTheory : Set₁ where
  field
    Mode : Set
    Res : Mode → Set

module ProofTheory (OT : ModeTheory) where
  open ModeTheory OT

  Reln : List Mode → Mode → Set₁
  Reln In Out = Mlist Res In → Res Out → Set

  Prop : Mode → Set₁
  Prop μs = Res μs → Set

  _✯_ : ∀ {ℓ ℓ'} {A : Set ℓ'} {F : A → Set ℓ} {ms : List A}
    → Mlist (λ μ → F μ → Set) ms → Mlist F ms → Set
  nil ✯ nil = Unit
  (p :: ps) ✯ (β :: βs) = p β × (ps ✯ βs)

  Mult Shift : (i : List Mode) {o : Mode} (ω : Reln i o) → Mlist Prop i → Prop o
  Mult i ω ps α = Σ (Mlist Res i) (λ βs → (ps ✯ βs) × ω βs α)
  Shift i ω ps α = Π (Mlist Res i) (λ βs → (ps ✯ βs) → ω βs α)
