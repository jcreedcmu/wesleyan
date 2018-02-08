{-# OPTIONS --without-K --rewriting #-}
module SharpRenamed where

open import HoTT hiding ( O; Path; _*_ )

module _ {ℓ} (C : Set ℓ) where
  postulate
    ♯ : Set
    ι : C → ♯
    Path : ∀ {ℓ} (A : ♯ → Set ℓ) (a : (c : C) → A (ι c)) → Set ℓ
    _*_ : ∀ {ℓ} {A : ♯ → Set ℓ} {a : (c : C) → A (ι c)}
      → Path A a → (i : ♯) → A i
    lam : ∀ {ℓ} {A : ♯ → Set ℓ} (f : (i : ♯) → A i)
      → Path A (f ∘ ι)
    ι-rewrite : ∀ {ℓ} {A : ♯ → Set ℓ} {a : (c : C) → A (ι c)}
      (p : Path A a) (c : C) → (p * (ι c)) ↦ a c
    {-# REWRITE ι-rewrite #-}

  syntax Path (λ i -> A) a = a ∈ i · A

  embu : ∀ {ℓ} {A : C → Set ℓ} (p : A ∈ i · Set ℓ)
    (a : (c : C) → A c) → Set ℓ
  embu {ℓ} {A} p a = a ∈ i · (p * i)

  embf : ∀ {ℓ} {A : ♯ → Set ℓ} {B : (i : ♯) (x : A i) → Set ℓ}
       {f : (c : C) → (x : A (ι c)) → B (ι c) x}
       → (f ∈ i · Π (A i) (B i))
       → ((x : (i : ♯) → A i) → (λ c → f c (x (ι c))) ∈ i · B i (x i))
  embf p x = lam (λ i → (p * i) (x i))

  postulate
    embu-equiv : ∀ {ℓ} {A : C → Set ℓ} → is-equiv (embu {ℓ} {A})
    embf-equiv : ∀ {ℓ} {A : ♯ → Set ℓ} {B : (i : ♯) (x : A i) → Set ℓ}
      {f : (c : C) (x : A (ι c)) → B (ι c) x}
      → is-equiv (embf {ℓ} {A} {B} {f})

-- What other things would I expect to see?
postulate
  -- Functoriality of ♯
  ♯F : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → ♯ A → ♯ B

  -- naturality of ι
  _ : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → ♯F f ∘ ι A == ι B ∘ f
