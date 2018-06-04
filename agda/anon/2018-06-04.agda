{-# OPTIONS --without-K --rewriting #-}
open import HoTT hiding ( _≤_ )

module 2018-06-04 where

postulate
  Δ : Set
  _≤_ : Δ → Δ → Set
  refl : (δ : Δ) → δ ≤ δ

apsnd : {A : Set} {B : A → Set} {t u : Σ A B} (p : t == u)
  → transport (B ∘ fst) p (snd t) == snd u
apsnd idp = idp

module Foo (A : Δ → Set) (B : (δ : Δ) → A δ → Set) where
  Am : (δ : Δ) → ((ε : Δ) → ε ≤ δ → A ε) → A δ
  Am δ f = f δ (refl δ)

  postulate
    Amie : (δ : Δ) → is-equiv (Am δ)

  -- A-transport could be implemented like so...
  At0 : (δ {ε} : Δ) → (a : A δ) → ε ≤ δ → A ε
  At0 δ {ε} a p = Amie δ .is-equiv.g a ε p

  At0red : (δ : Δ) → (a : A δ) → At0 δ a (refl δ) == a
  At0red δ a = Amie δ .is-equiv.f-g a

  postulate
    -- but we postulate it instead so we can do rewriting to cheaply
    -- prototype whether this proof has a chance of working.
    At : ({δ} {ε} : Δ) → (a : A δ) → ε ≤ δ → A ε
    Atred : (δ : Δ) → (a : A δ) → At a (refl δ) ↦ a
    {-# REWRITE Atred #-}

  Bm : (δ : Δ) (a : A δ) → B δ a → (Σ Δ (λ ε → Σ (ε ≤ δ) (λ p → B ε (At a p))))
  Bm δ a b = δ , (refl δ , b)

  postulate
    Bmie : (δ : Δ) (a : A δ) → is-equiv (Bm δ a)

  -- B-transport could be implemented like so...
  Bt0 : {δ ε : Δ} (a : A δ) (p : ε ≤ δ) → B ε (At a p) → B δ a
  Bt0 {δ} {ε} a p b = Bmie δ a .is-equiv.g (ε , (p , b))
  -- ???
  Bt0red : {δ : Δ} (a : A δ) (b : B δ a) → Bt0 a (refl δ) b == b
  Bt0red {δ} a b = {!Bmie δ a .is-equiv.f-g (δ , (refl δ , b))!}

  postulate
    -- but we postulate it instead so we can do rewriting to cheaply
    -- prototype whether this proof has a chance of working.
    Bt : {δ ε : Δ} (a : A δ) (p : ε ≤ δ) → B ε (At a p) → B δ a
    Btred : {δ : Δ} (a : A δ) (b : B δ a) → Bt a (refl δ) b ↦ b
    {-# REWRITE Btred #-}

  -- Pi type
  AB : (δ : Δ) → Set
  AB δ = (a : A δ) → B δ a

  -- Reflexivity morphism for Pi type:
  ABm : (δ : Δ) → AB δ → Σ Δ (λ ε → (ε ≤ δ) × AB ε)
  ABm δ f = δ , (refl δ , f)

  -- Lemmas
  ABmi : (δ : Δ) → Σ Δ (λ ε → (ε ≤ δ) × AB ε) → AB δ
  ABmi δ (ε , (p , f)) a = Bt a p (f (At a p))

  -- GOAL:
  ABmie : (δ : Δ) → is-equiv (ABm δ)
  ABmie δ = is-eq (ABm δ) (ABmi δ) zig zag where
    zig : (b : Σ Δ (λ ε → (ε ≤ δ) × AB ε)) → ABm δ (ABmi δ b) == b
    -- need: δ , refl δ , (λ a → Bt a p (f (At a p))) == ε , p , f
    zig (ε , p , f) = {!λ a → Bmie δ a .is-equiv.g-f!}
    zag : (a : AB δ) → ABmi δ (ABm δ a) == a
    zag f = idp
{-

Want to somehow transform

(λ a → Bt a p (f (At a p)))

suspect I need

λ a → Bmie δ a .is-equiv.g-f

somehow, which is of type

  (a : A δ) (a₁ : B δ a) →
      is-equiv.g (Bmie δ a) (Bm δ a a₁) == a₁

which does look roughly like

  (a : A δ) (a₁ : B δ a) →
      Bt0 (Bm δ a a₁) == a₁ (*XXX*)

but things don't line up quite right for that to be well-typed
-}
