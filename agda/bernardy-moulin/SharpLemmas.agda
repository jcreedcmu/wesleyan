{-# OPTIONS --without-K --rewriting #-}
module SharpLemmas where

open import HoTT hiding ( O; Path; _*_ )
import Sharp

module WithArity (C : Set) where
  open Sharp.WithArity C

  Cset : ∀ {ℓ} → Set (lsucc ℓ)
  Cset {ℓ} = C → Set ℓ

  φ : ∀ {ℓ} → Cset → Set ℓ
  φ A = (c : C) → A c

  embu-inv : ∀ {ℓ} {A : Cset}
    → (φ A → Set ℓ) → A ∈ i · Set ℓ
  embu-inv {ℓ} {A} = embu-equiv .is-equiv.g

  embu-fg : ∀ {ℓ} {A : Cset} (P : φ A → Set ℓ)
    → embu (embu-inv P) == P
  embu-fg {ℓ} {A} = embu-equiv .is-equiv.f-g

  embf-inv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
       {f : (c : C) → (x : A (η c)) → B (η c) x}
       → ((x : (i : 𝕀) → A i) → (λ c → f c (x (η c))) ∈ i · B i (x i))
       → (f ∈ i · Π (A i) (B i))
  embf-inv {ℓ} {A} = embf-equiv .is-equiv.g


  embu-round : {A : Cset} (P : φ A → Set) (a : φ A)
               → P a → embu (embu-inv P) a
  embu-round P a p = coe (app= (! (embu-fg P)) a) p

  embu-round2 : {A : Cset} (P : φ A → Set) (a : φ A)
              → embu (embu-inv P) a → P a
  embu-round2 P a t = coe (app= (embu-fg P) a) t

  freeThm-id : (f : (X : Set) → X → X) (A : Cset) (P : φ A → Set) (a : φ A) (p : P a) → P (λ c → f (A c) (a c))
  freeThm-id f A P a p = embu-round2 P (λ c → f (A c) (a c)) path where
    ww : (i : 𝕀) → Set
    ww i = embu-inv P * i
    pp : (i : 𝕀) → ww i
    pp i = embu-round P a p * i
    app : (i : 𝕀) → ww i
    app i = f (ww i) (pp i)
    path : (λ c → f (A c) (a c)) ∈ i · ww i
    path = lam app

  freeThm-nat : (f : (X : Set) → X → (X → X) → X) (A : Cset) (P : φ A → Set)
              (z : φ A) (zp : P z)
              (s : φ (λ c → A c → A c))
              (sp : (x : φ A) → P x → P (λ c → s c (x c)))
              → P (λ c → f (A c) (z c) (s c))
  freeThm-nat f A P z zp s sp = embu-round2 P output path where
    output = (λ c → f (A c) (z c) (s c))
    ww : (i : 𝕀) → Set
    ww i = embu-inv P * i
    suc : Π 𝕀 ww → φ A
    suc x c = s c (x (η c))
    spp : (x : (i : 𝕀) → ww i) → P (suc x)
    spp x = sp (x ∘ η) (embu-round2 P (x ∘ η) (lam x))
    s4 : s ∈ i · (ww i → ww i)
    s4 = embf-inv (λ x → embu-round P (suc x) (spp x))
    s5 : (i : 𝕀) → ww i → ww i
    s5 i = s4 * i
    app : (i : 𝕀) → ww i
    app i = f (ww i) (embu-round P z zp * i) (s5 i)
    path : output ∈ i · ww i
    path = lam app
