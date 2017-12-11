{-# OPTIONS --without-K --rewriting #-}
module Sharp1 where

open import HoTT hiding ( O; Path; _*_ )

postulate
  𝕀 : Set
  O : 𝕀
  Path : ∀ {ℓ} (A : 𝕀 → Set ℓ) (a : A O) → Set ℓ
  _*_ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O}
    → Path A a → (i : 𝕀) → A i
  lam : ∀ {ℓ} {A : 𝕀 → Set ℓ} (f : (i : 𝕀) → A i)
    → Path A (f O)
  O-rewrite : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O}
    (p : Path A a) → (p * O) ↦ a
  {-# REWRITE O-rewrite #-}

syntax Path (λ i -> A) a = a ∈ i · A

embu : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ)
  (a : A) → Set ℓ
embu {ℓ} {A} p a = a ∈ i · (p * i)

embf : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
     {f : (x : A O) → B O x}
     → (f ∈ i · Π (A i) (B i))
     → ((x : (i : 𝕀) → A i) → (f (x O)) ∈ i · B i (x i))
embf p x = lam (λ i → (p * i) (x i))

postulate
  embu-equiv : ∀ {ℓ} {A : Set ℓ} → is-equiv (embu {ℓ} {A})
  embf-equiv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
    {f : (x : A O) → B O x}
    → is-equiv (embf {ℓ} {A} {B} {f})
