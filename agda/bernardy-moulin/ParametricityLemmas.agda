{-# OPTIONS --without-K --rewriting #-}
module ParametricityLemmas where

open import Parametricity
open import HoTT hiding ( O; Path; _*_) renaming (! to rev)
-- (https://github.com/HoTT/HoTT-Agda)

-- Defining the operations in Moulin's thesis in terms of what we have
-- postulated:

_! : ∀ {ℓ} {A : 𝕀 → Set ℓ} (u : (i : 𝕀) → A i) → u O ∈ i · (A i)
_! = lam

⦅_,_⦆ : ∀ {ℓ} {A : 𝕀 → Set ℓ} (a : A O) (p : a ∈ i · A i) → ((i : 𝕀) → A i)
⦅_,_⦆ a p i = p * i

-- This inverse is the Ψ_A used in rule IN-PRED (cf. Moulin's thesis, p88)
Ψ : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) → A ∈ i · Set ℓ
Ψ P = embu-equiv .is-equiv.g P

-- This inverse is the Φ_t used in rule IN-FUN (cf. Moulin's thesis, p88)
Φ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
  → (t : (x : A O) → B O x)
  → (u : (x : (i : 𝕀) → A i) → (t (x O)) ∈ i · B i (x i))
  → t ∈ i · ((x : A i) → B i x)
Φ t u = embf-equiv t .is-equiv.g u

_⋈_ : ∀ {ℓ} (A : Set ℓ) (P : A → Set ℓ) (i : 𝕀) → Set ℓ
A ⋈ P = ⦅ A , Ψ P ⦆

⦉_,_⦊ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
    → (t : (x : A O) → B O x)
    → (u : (x : (i : 𝕀) → A i) → (t (x O)) ∈ i · B i (x i))
    → (i : 𝕀) (x : A i) → B i x
⦉ t , u ⦊ = ⦅ t , Φ t u ⦆

-- Some lemmas for what follows
module _ where
  embu-inv : ∀ {ℓ} {A : Set ℓ}
    → (A → Set ℓ) → A ∈ i · Set ℓ
  embu-inv {ℓ} {A} = embu-equiv .is-equiv.g

  embu-fg : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ)
    → embu (embu-inv P) == P
  embu-fg {ℓ} {A} = embu-equiv .is-equiv.f-g

  embu-coe : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) (a : A)
               → P a → embu (embu-inv P) a
  embu-coe P a p = coe (app= (rev (embu-fg P)) a) p

  embu-coe2 : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) (a : A)
              → embu (embu-inv P) a → P a
  embu-coe2 P a t = coe (app= (embu-fg P) a) t

  round-trip :  ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ}
    (π : P == Q) (a : A) (z : P a) →
    coe (app= (rev π) a) (coe (app= π a) z) == z
  round-trip idp a z = idp

  round-trip2 :  ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ}
    (π : P == Q) (a : A) (z : Q a) →
    coe (app= π a) (coe (app= (rev π) a) z) == z
  round-trip2 idp a z = idp

-- The conversion-relation axioms fall out of these definitions:
-- (cf. Moulin's thesis, p89)
PAIR-ORIG : {A : 𝕀 → Set} (a : A O) (p : a ∈ i · A i) →
  ⦅ a , p ⦆ O == a
PAIR-ORIG a p = idp

PAIR-PARAM : {A : 𝕀 → Set} (a : A O) (p : a ∈ i · A i) →
  (⦅ a , p ⦆ !) == p
PAIR-PARAM a p = idp

SURJ-PARAM : {A : 𝕀 → Set} (u : (i : 𝕀) → A i) →
  ⦅ u O , u ! ⦆ == u
SURJ-PARAM u = idp

PAIR-PRED : ∀ {ℓ} (A : Set ℓ) (P : A → Set ℓ) (a : A) →
  P a == (a ∈ i · (A ⋈ P) i)
PAIR-PRED A P a = ua (equiv into out zig zag) where
  into : P a → Path (A ⋈ P) a
  into = embu-coe P a
  out : Path (A ⋈ P) a → P a
  out = embu-coe2 P a
  zig : (b : Path (A ⋈ P) a) → into (out b) == b
  zig b = round-trip (embu-fg P) a b
  zag : (b : P a) → out (into b) == b
  zag b = round-trip2 (embu-fg P) a b

PAIR-APP : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
  → (t : (x : A O) → B O x)
  → (u : (x : (i : 𝕀) → A i) → (t (x O)) ∈ i · B i (x i))
  → (i : 𝕀) (a : (i : 𝕀) → A i)
  → ⦉_,_⦊ {B = B} t u i (a i) == ⦅ t (a O) , u a ⦆ i
PAIR-APP {B = B} t u i a = normalized-goal where
  before-ap : embf (is-equiv.g (embf-equiv t) u) a == u a
  before-ap = app= (embf-equiv {B = B} t .is-equiv.f-g u) a
  normalized-goal : (embf-equiv {B = B} t .is-equiv.g u * i) (a i) == (u a * i)
  normalized-goal = ap (λ z → z * i) before-ap

SURJ-TYPE : ∀ {ℓ} (A : 𝕀 → Set ℓ) →
  Ψ {A = A O} (λ x → x ∈ i · (A i)) == (A !)
SURJ-TYPE A = embu-equiv .is-equiv.g-f (lam A)

SURJ-FUN : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
  → (t : (i : 𝕀) (x : A i) → B i x)
  → Φ (t O) (λ x → (λ i → t i (x i)) !) == (t !)
SURJ-FUN {B = B} t = embf-equiv (t O) .is-equiv.g-f (lam t)
