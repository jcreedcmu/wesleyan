{-# OPTIONS --without-K --rewriting #-}
open import HoTT hiding ( _≤_ )

module 2018-06-05 where

postulate
  Δ : Set
  _≤_ : Δ → Δ → Set
  refl : (δ : Δ) → δ ≤ δ
  comp : {a b c : Δ} → a ≤ b → b ≤ c → a ≤ c

  compl : {a b : Δ} (f : a ≤ b) → comp (refl a) f ↦ f
  compr : {a b : Δ} (f : a ≤ b) → comp f (refl b) ↦ f
  {-# REWRITE compl compr #-}

module Foo (A : Δ → Set) (B : (δ : Δ) → A δ → Set) where

  postulate
    -- but we postulate it instead so we can do rewriting to cheaply
    -- prototype whether this proof has a chance of working.
    At : ({δ} {ε} : Δ) → (a : A δ) → ε ≤ δ → A ε
    At-β : (δ : Δ) → (a : A δ) → At a (refl δ) ↦ a
    At-η : (δ : Δ) (q : (ε : Δ) → ε ≤ δ → A ε) (a : A δ)
--      → q δ (refl δ) == a
      → q == λ ε → At {ε = ε} (q δ (refl δ))
    {-# REWRITE At-β #-}

--   Bm : (δ : Δ) (a : A δ) → B δ a → (Σ Δ (λ ε → Σ (ε ≤ δ) (λ p → B ε (At a p))))
--   Bm δ a b = δ , (refl δ , b)


  record Bl (δ : Δ) (a : A δ) : Set where
    constructor bl
    field
      ε : Δ
      p : ε ≤ δ
      b : B ε (At a p)

  postulate
    -- but we postulate it instead so we can do rewriting to cheaply
    -- prototype whether this proof has a chance of working.
    Bt : {δ ε : Δ} (a : A δ) (p : ε ≤ δ) → B ε (At a p) → B δ a
    Bt-β : {δ : Δ} (a : A δ) (b : B δ a) → Bt a (refl δ) b ↦ b
    Bt-η : (δ : Δ) (a : A δ) (q : Bl δ a) →
      q == bl δ (refl δ) (Bt a (q .Bl.p) (q .Bl.b))

    {-# REWRITE Bt-β #-}

  -- Pi type
  AB : (δ : Δ) → Set
  AB δ = (a : A δ) → B δ a

  record ABl (δ : Δ) : Set where
    constructor abl
    field
      ε : Δ
      p : ε ≤ δ
      f : AB ε

  -- Reflexivity morphism for Pi type:
  ABm : (δ : Δ) → AB δ → ABl δ
  ABm δ f = abl δ (refl δ) f

  -- Transport at ΠAB
  ABmi : (δ : Δ) → ABl δ → AB δ
  ABmi δ (abl ε p f) a = Bt a p (f (At a p))

  {- given this transport, it seems possible to conjecture
     a principle of coend equivalence like so -}
  postulate
    ABq : (δ me ne : Δ) (p1 : me ≤ ne) (p2 : ne ≤ δ)
      (mf : (x : A me) → B me x) →
      (abl ne p2 (ABmi ne (abl me p1 mf))) == (abl me (comp p1 p2) mf)

  -- GOAL:
  ABmie : (δ : Δ) → is-equiv (ABm δ)
  ABmie δ = is-eq (ABm δ) (ABmi δ) zig zag where
    zig : (b : ABl δ) → ABm δ (ABmi δ b) == b
    zig (abl ε p f) = ABq δ ε δ p (refl δ) f
    zag : (a : AB δ) → ABmi δ (ABm δ a) == a
    zag f = idp
