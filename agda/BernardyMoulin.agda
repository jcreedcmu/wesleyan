module BernardyMoulin where
-- {-# OPTIONS --type-in-type #-}

postulate
  𝕀 : Set
  O : 𝕀
  Path : ∀ {ℓ} → (A : 𝕀 → Set ℓ) → A O → Set ℓ

syntax Path (λ i -> A) a = a ∈ i · A
-- syntax Path (λ i -> A) a = i · A ∋ a

postulate
  _! : {A : 𝕀 → Set} (u : (i : 𝕀) → A i) → u O ∈ i · A i
  -- agda won't let me say ⦇_,_⦈ for this:
  ppair : {A : 𝕀 → Set} (a : A O) (p : a ∈ i · A i) → (i : 𝕀) → A i

  Ψ : {A : Set} (P : A → Set) → A ∈ i · Set
  Φ : {A : 𝕀 → Set} {B : (i : 𝕀) (x : A i) → Set}
      {t : (x : A O) → B O x}
      (u : (x : (i : 𝕀) → A i) → (t (x O) ∈ i · B i (x i)))
      → t ∈ i · ((x : A i) → B i x)

Φlem : {A : 𝕀 → Set} {B : (i : 𝕀) (x : A i) → Set}
       (u : (x : (i : 𝕀) → A i) → ((i : 𝕀) → B i (x i)))
     → ((i : 𝕀) → ((x : A i) → B i x))
Φlem u = {!λ x → u x O!}


module Lemma (X : 𝕀 → Set) where
  M1 : ((i : 𝕀) (j : 𝕀) → X i) → ((i : 𝕀) (j : 𝕀) → X j)
  M1 = λ f i j → f j i

  M2 : (f : (i : 𝕀) (j : 𝕀) → X i) → (λ j → f j O) ∈ i · ((j : 𝕀) → X j)
  M2 = λ f → (M1 f) !

  M3 : {!!}
  M3 = Φ {A = λ i → (j : 𝕀) → X i} {B = λ _ _ → (j : 𝕀) → X j}
         {t = λ x j → {!!}} {!!}
