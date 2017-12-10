{-# OPTIONS --without-K #-}
module BernardyMoulin3 where

-- {-# OPTIONS --type-in-type #-}

open import HoTT hiding ( O; Path; _*_)

postulate
  𝕀 : Set
  O : 𝕀

Path : ∀ {ℓ} (A : 𝕀 → Set ℓ) → A O → Set ℓ
Path A a = Σ ((i : 𝕀) → A i) (λ f → a == f O)
syntax Path (λ i -> A) a = a ∈ i · A

_*_ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O} → (a ∈ i · A i) → (i : 𝕀) → A i
p * i = p .fst i

embu : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ) (a : A) → Set ℓ
embu {ℓ} {A} p a = (coe (p .snd) a) ∈ i · (p * i)

postulate
  embu-equiv : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ) → is-equiv (embu p)

embf : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
  → (f ∈ i · Π (A i) (B i)) → ((x : (i : 𝕀) → A i) → f (x O) ∈ i · B i (x i))
embf p x = (λ i → (p * i) (x i)) , (app= (p .snd) (x O))

postulate
  embf-equiv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
    → is-equiv (embf {ℓ} {A} {B} {f})
