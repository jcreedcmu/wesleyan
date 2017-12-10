{-# OPTIONS --without-K --rewriting #-}
module Sharp where

open import HoTT hiding ( O; Path; _*_ )

module WithArity (C : Set) where
  postulate
    ♯ : Set
    η : C → ♯
    Path : ∀ {ℓ} (A : ♯ → Set ℓ) (a : (c : C) → A (η c)) → Set ℓ
    _*_ : ∀ {ℓ} {A : ♯ → Set ℓ} {a : (c : C) → A (η c)}
      → Path A a → (i : ♯) → A i
    lam : ∀ {ℓ} {A : ♯ → Set ℓ} (f : (i : ♯) → A i)
      → Path A (f ∘ η)
    η-rewrite : ∀ {ℓ} {A : ♯ → Set ℓ} {a : (c : C) → A (η c)}
      (p : Path A a) (c : C) → (p * (η c)) ↦ a c
    {-# REWRITE η-rewrite #-}

  syntax Path (λ i -> A) a = a ∈ i · A

  embu : ∀ {ℓ} {A : C → Set ℓ} (p : A ∈ i · Set ℓ)
    (a : (c : C) → A c) → Set ℓ
  embu {ℓ} {A} p a = a ∈ i · (p * i)

  embf : ∀ {ℓ} {A : ♯ → Set ℓ} {B : (i : ♯) (x : A i) → Set ℓ}
       {f : (c : C) → (x : A (η c)) → B (η c) x}
       → (f ∈ i · Π (A i) (B i))
       → ((x : (i : ♯) → A i) → (λ c → f c (x (η c))) ∈ i · B i (x i))
  embf p x = lam (λ i → (p * i) (x i))

  postulate
    embu-equiv : ∀ {ℓ} {A : C → Set ℓ} → is-equiv (embu {ℓ} {A})
    embf-equiv : ∀ {ℓ} {A : ♯ → Set ℓ} {B : (i : ♯) (x : A i) → Set ℓ}
      {f : (c : C) (x : A (η c)) → B (η c) x}
      → is-equiv (embf {ℓ} {A} {B} {f})
