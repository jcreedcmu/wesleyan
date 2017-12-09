{-# OPTIONS --without-K #-}
module BernardyMoulin2 where

-- {-# OPTIONS --type-in-type #-}

open import HoTT hiding ( O; Path) renaming (! to ‼)

x = is-equiv

postulate
  𝕀 : Set
  O : 𝕀
  uar : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → (Σ (𝕀 → Set ℓ) (λ C → A == C O))
  uar-equiv : ∀ {ℓ} {A : Set ℓ} → is-equiv (uar {ℓ} {A})

uai : ∀ {ℓ} {A : Set ℓ} → (Σ (𝕀 → Set ℓ) (λ C → A == C O)) → (A → Set ℓ)
uai = uar-equiv .is-equiv.g

uai,uar : ∀ {ℓ} {A : Set ℓ} (q : A → Set ℓ) → uai (uar q) == q
uai,uar = uar-equiv .is-equiv.g-f

uar,uai : ∀ {ℓ} {A : Set ℓ} (q : (Σ (𝕀 → Set ℓ) (λ C → A == C O))) → uar (uai q) == q
uar,uai = uar-equiv .is-equiv.f-g

_⋆_ : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → 𝕀 → Set ℓ
R ⋆ i = uar R .fst i

/ : ∀ {ℓ} {A : Set ℓ} {R : A → Set ℓ} → A → R ⋆ O
/ {R = R} a = coe (uar R .snd) a

// : ∀ {ℓ} {A : Set ℓ} {R : A → Set ℓ} → R ⋆ O → A
// {R = R} a = coe (‼ (uar R .snd)) a

natlem1 : ∀ {ℓ} → {A B : Set ℓ} (P : ({C : Set ℓ} → (C == B) → C → Set ℓ))
        (p : A == B) (a : A) → P idp (coe p a) == P p a
natlem1 P idp a = idp

natlem2 : ∀ {ℓ} {A : Set ℓ} (R : A → Set ℓ) (a : A)  →
    uai ((λ i → R ⋆ i) , idp) (/ a) ==
    uai ((λ i → R ⋆ i) , uar R .snd) a
natlem2 R a = natlem1 (λ x y → uai ((λ i → R ⋆ i) , x) y) (uar R .snd) a

Path : ∀ {ℓ} → (A : 𝕀 → Set ℓ) → A O → Set ℓ
Path A a = uai {A = A O} (A , idp) a
syntax Path (λ i -> A) a = a ∈ i · A

pairPred : ∀ {ℓ} {A : Set ℓ} (R : A → Set ℓ) (a : A) → ((/ a) ∈ i · (R ⋆ i)) == R a
pairPred R a = natlem2 R a ∙ app= (uai,uar R) a

pairPredX : ∀ {ℓ} {A : Set ℓ} (R : A → Set ℓ) (a : R ⋆ O) → (a ∈ i · (R ⋆ i)) == R (// a)
pairPredX R a = {!!}

pairPredY : ∀ {ℓ} (A : 𝕀 → Set ℓ) (a : A O) → (a ∈ i · A i) == Path A a
pairPredY A a = {!!}

_! : {A : 𝕀 → Set} (u : (i : 𝕀) → A i) → u O ∈ i · A i
_! {A} u = {!uai ((λ i → A i) , idp) (u O)!}

postulate

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
