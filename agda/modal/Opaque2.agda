open import HoTT
-- This is a more standalone version of Opaque.agda, but we're not
-- even thinking of the translation as a translation per se, just a
-- design pattern whereby we simply show how to construct
-- substructural propositions from others.
module Opaque2 where

data Mlist {ℓ ℓ'} {U : Set ℓ} (El : U → Set ℓ') : List U → Set (lmax ℓ ℓ') where
  nil : Mlist El nil
  _::_ : {A : U} {L : List U} → El A → Mlist El L → Mlist El (A :: L)

data Post : Set where -- postures
  mult shft : Post

record ModeTheory : Set₁ where
  field
    Mode : Set
    Res : Mode → Set

module ProofTheory (OT : ModeTheory) where
  open ModeTheory OT

  record Opr (π : Post) : Set₁ where
    field
      Input : List Mode
      Output : Mode
      Reln : Mlist Res Input → Res Output → Set
  open Opr

  Prop : Mode → Set₁
  Prop μs = Res μs → Set

  _✯_ : ∀ {ℓ ℓ'} {A : Set ℓ'} {F : A → Set ℓ} {ms : List A}
    → Mlist (λ μ → F μ → Set) ms → Mlist F ms → Set
  nil ✯ nil = Unit
  (p :: ps) ✯ (β :: βs) = p β × (ps ✯ βs)

  C : {π : Post} (ω : Opr π) → Mlist Prop (Input ω) → Prop (Output ω)
  C {mult} ω ps α = Σ (Mlist Res (Input ω)) (λ βs → (ps ✯ βs) × Reln ω βs α)
  C {shft} ω ps α = Π (Mlist Res (Input ω)) (λ βs → (ps ✯ βs) → Reln ω βs α)
