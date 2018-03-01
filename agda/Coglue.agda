{-# OPTIONS --without-K --rewriting #-}
module Coglue where

open import HoTT hiding ( O; Path; _*_ )

postulate
  𝕀 : Set
  O : 𝕀
  Path : ∀ {ℓ} (A : 𝕀 → Set ℓ) (a : A O) → Set ℓ
  _*_ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O}
    → Path A a → (i : 𝕀) → A i
  lam : ∀ {ℓ} {A : 𝕀 → Set ℓ} (f : (i : 𝕀) → A i) → Path A (f O)
  O-rewrite : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O}
    (p : Path A a) → (p * O) ↦ a
  {-# REWRITE O-rewrite #-}

syntax Path (λ i -> A) a = a ∈ i · A

embu : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ)
  (a : A) → Set ℓ
embu {ℓ} {A} p a = a ∈ i · (p * i)

postulate
  coglue : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → A ∈ i · Set ℓ

embu-equiv : ∀ {ℓ} {A : Set ℓ} → is-equiv (embu {ℓ} {A})
embu-equiv {ℓ} {A} = is-eq embu coglue zig zag where

  ziga : (b : A → Set ℓ) (a : A) → embu (coglue b) a ≃ b a
  ziga b a = equiv inj out {!!} {!!} where
    inj : embu (coglue b) a → b a
    inj = {!a ∈ i · coglue b * i!}
    out : b a → embu (coglue b) a
    out = {!!}

  zig : (b : A → Set ℓ) → embu (coglue b) == b
  zig b = λ= (λ a → ua (ziga b a))
  zag : (a : A ∈ i · Set ℓ) → coglue (embu a) == a
  zag = {!!}
