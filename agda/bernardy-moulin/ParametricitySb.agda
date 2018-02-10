{-# OPTIONS --without-K --rewriting #-}
module ParametricitySb where

open import HoTT hiding ( O; Path; _*_) renaming (! to rev)
open import Parametricity
open import ParametricityLemmas

pair=1 : ∀ {i j} {A : Type i} {B : A → Type j}
  {a : A} {b b' : B a}
  (q : b == b')
  → pair {B = B} a b == (a , b')
pair=1 idp = idp


thm : (𝕀 → Set) == Σ Set (λ A → A → Set)
thm = ua (equiv into out zig zag) where
  into : (𝕀 → Set) → Σ Set (λ A → A → Set)
  into f = f O , embu (f !)

  out : Σ Set (λ A → A → Set) → (𝕀 → Set)
  out b i = Ψ (b .snd) * i

  zig : (b : Σ Set (λ A → A → Set)) → into (out b) == b
  zig b = pair=1 (embu-fg (snd b))

  zag : (a : 𝕀 → Set) → (λ i → embu-inv (embu (lam a)) * i) == a
  zag a = λ= (λ i → ap (λ z → z * i) (embu-equiv .is-equiv.g-f (a !)))
