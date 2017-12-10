{-# OPTIONS --without-K --rewriting #-}
module BernardyMoulin5 where

open import HoTT hiding ( O; Path; _*_ )
import Sharp

module Sh = Sharp.WithArity ⊤
open Sh using ( η ; 𝕀 )

O : 𝕀
O = η tt

Path : ∀ {ℓ} (A : 𝕀 → Set ℓ) → A O → Set ℓ
Path A a = Sh.Path A (λ _ → a)

_*_ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O} → Path A a → (i : 𝕀) → A i
_*_ = Sh._*_

lam : ∀ {ℓ} {A : 𝕀 → Set ℓ} (f : (i : 𝕀) → A i) → Path A (f O)
lam = Sh.lam

syntax Path (λ i -> A) a = a ∈ i · A

embu : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ) (a : A) → Set ℓ
embu {ℓ} {A} p a  = Sh.embu {ℓ} {λ _ → A} p (λ _ → a)

-- ugh still too bored, it hinges on the equality of A and ⊤ → A

-- embu-equiv0 : ∀ {ℓ} {A : Set ℓ} → is-equiv (λ p a → embu {ℓ} {A} p a)
embu-equiv0 : ∀ {ℓ} {A : Set ℓ} → is-equiv (λ p a → Sh.embu {ℓ} {λ _ → A} p a)
embu-equiv0 {ℓ} {A} = Sh.embu-equiv {ℓ} {λ _ → A}


-- embu-inv : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → A ∈ i · Set ℓ
-- embu-inv {ℓ} {A} = embu-equiv .is-equiv.g

-- embu-fg : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) → embu (embu-inv P) == P
-- embu-fg {ℓ} {A} = embu-equiv .is-equiv.f-g

-- embf : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
--   → (f ∈ i · Π (A i) (B i)) → ((x : (i : 𝕀) → A i) → f (x O) ∈ i · B i (x i))
-- embf p x = lam (λ i → (p * i) (x i))

-- postulate
--   embf-equiv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
--     → is-equiv (embf {ℓ} {A} {B} {f})

-- embf-inv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
--   → ((x : (i : 𝕀) → A i) → f (x O) ∈ i · B i (x i)) → (f ∈ i · Π (A i) (B i))
-- embf-inv {ℓ} {A} = embf-equiv .is-equiv.g


-- -- embu (embu-inv P) a = a ∈ i · (embu-inv P * i)
-- embu-round : {A : Set} (P : A → Set) (a : A)
--              → P a → embu (embu-inv P) a
-- embu-round P a p = coe (app= (! (embu-fg P)) a) p

-- embu-round2 : {A : Set} (P : A → Set) (a : A)
--              → embu (embu-inv P) a → P a
-- embu-round2 P a t = coe (app= (embu-fg P) a) t

-- freeThm-id : (f : (X : Set) → X → X) (A : Set) (P : A → Set) (a : A) (p : P a) → P (f A a)
-- freeThm-id f A P a p = embu-round2 P (f A a) path where
--   ww : (i : 𝕀) → Set
--   ww i = embu-inv P * i
--   pp : (i : 𝕀) → ww i
--   pp i = embu-round P a p * i
--   app : (i : 𝕀) → ww i
--   app i = f (ww i) (pp i)
--   path : (f A a) ∈ i · ww i
--   path = lam app

-- freeThm-nat : (f : (X : Set) → X → (X → X) → X) (A : Set) (P : A → Set)
--             (z : A) (zp : P z) (s : A → A) (sp : (x : A) → P x → P (s x))
--             → P (f A z s)
-- freeThm-nat f A P z zp s sp = embu-round2 P (f A z s) path where
--   ww : (i : 𝕀) → Set
--   ww i = embu-inv P * i
--   pp : (i : 𝕀) → ww i
--   pp i = embu-round P z zp * i
--   spp : (x : (i : 𝕀) → ww i) → P (s (x O))
--   spp x = sp (x O) (embu-round2 P (x O) (lam x))
--   s3 : (x : (i : 𝕀) → ww i) → (s (x O)) ∈ i · (embu-inv P * i)
--   s3 x = embu-round P (s (x O)) (spp x)
--   s4 : s ∈ i · (ww i → ww i)
--   s4 = embf-inv s3
--   s5 : (i : 𝕀) → ww i → ww i
--   s5 i = s4 * i
--   app : (i : 𝕀) → ww i
--   app i = f (ww i) (pp i) (s5 i)
--   path : (f A z s) ∈ i · ww i
--   path = lam app
