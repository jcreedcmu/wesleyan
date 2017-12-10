{-# OPTIONS --without-K --rewriting #-}
module Sharp where

open import HoTT hiding ( O; Path; _*_ )

postulate
  ♯ : Set → Set
  η : {C : Set} → C → ♯ C
  Path : ∀ {ℓ} {C : Set} (A : ♯ C → Set ℓ) (a : (c : C) → A (η c)) → Set ℓ
  _*_ : ∀ {ℓ} {C : Set} {A : ♯ C → Set ℓ} {a : (c : C) → A (η c)}
    → Path A a → (i : ♯ C) → A i
  lam : ∀ {ℓ} {C : Set} {A : ♯ C → Set ℓ} (f : (i : ♯ C) → A i)
    → Path A (f ∘ η)
  η-rewrite : ∀ {ℓ} {C : Set} {A : ♯ C → Set ℓ} {a : (c : C) → A (η c)}
    (p : Path A a) (c : C) → (p * (η c)) ↦ a c
  {-# REWRITE η-rewrite #-}

syntax Path (λ i -> A) a = a ∈ i · A

embu : ∀ {ℓ} {C : Set} {A : C → Set ℓ} (p : A ∈ i · Set ℓ)
  (a : (c : C) → A c) → Set ℓ
embu {ℓ} {C} {A} p a = a ∈ i · (p * i)

embf : ∀ {ℓ} {C : Set} {A : ♯ C → Set ℓ} {B : (i : ♯ C) (x : A i) → Set ℓ}
     {f : (c : C) → (x : A (η c)) → B (η c) x}
     → (f ∈ i · Π (A i) (B i))
     → ((x : (i : ♯ C) → A i) → (λ c → f c (x (η c))) ∈ i · B i (x i))
embf p x = lam (λ i → (p * i) (x i))

postulate
  embu-equiv : ∀ {ℓ} {C : Set} {A : C → Set ℓ} → is-equiv (embu {ℓ} {C} {A})
  embf-equiv : ∀ {ℓ} {C : Set} {A : ♯ C → Set ℓ} {B : (i : ♯ C) (x : A i) → Set ℓ}
    {f : (c : C) (x : A (η c)) → B (η c) x}
    → is-equiv (embf {ℓ} {C} {A} {B} {f})
