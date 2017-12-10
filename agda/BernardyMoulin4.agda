{-# OPTIONS --without-K --rewriting #-}
module BernardyMoulin4 where

-- postulate
--   Foo : Set
--   𝕥 𝕗 : Foo

--   𝕥-rewrite : 𝕥 ↦ 𝕗
--   {-# REWRITE 𝕥-rewrite #-}

-- x : 𝕥 == 𝕗
-- x = idp

open import HoTT hiding ( O; Path; _*_)

postulate
  𝕀 : Set
  O : 𝕀

  Path : ∀ {ℓ} (A : 𝕀 → Set ℓ) → A O → Set ℓ
  _*_ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O} → Path A a → (i : 𝕀) → A i
  lam : ∀ {ℓ} {A : 𝕀 → Set ℓ} (f : (i : 𝕀) → A i) → Path A (f O)

syntax Path (λ i -> A) a = a ∈ i · A

postulate
  O-rewrite : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O} (p : a ∈ i · A i) → (p * O) ↦ a
  {-# REWRITE O-rewrite #-}

-- _//_ : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ) (a : A) → p * O
-- p // a = coe (p .snd) a

embu : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ) (a : A) → Set ℓ
embu {ℓ} {A} p a = a ∈ i · (p * i)

postulate
  embu-equiv : ∀ {ℓ} {A : Set ℓ} → is-equiv (embu {ℓ} {A})

embu-inv : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → A ∈ i · Set ℓ
embu-inv {ℓ} {A} = embu-equiv .is-equiv.g

embu-fg : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) → embu (embu-inv P) == P
embu-fg {ℓ} {A} = embu-equiv .is-equiv.f-g

embf : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
  → (f ∈ i · Π (A i) (B i)) → ((x : (i : 𝕀) → A i) → f (x O) ∈ i · B i (x i))
embf p x = lam (λ i → (p * i) (x i))

postulate
  embf-equiv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
    → is-equiv (embf {ℓ} {A} {B} {f})

embf-inv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
  → ((x : (i : 𝕀) → A i) → f (x O) ∈ i · B i (x i)) → (f ∈ i · Π (A i) (B i))
embf-inv {ℓ} {A} = embf-equiv .is-equiv.g

embu-round : {A : Set} (P : A → Set) (a : A)
             → P a → embu (embu-inv P) a
embu-round P a p = coe (app= (! (embu-fg P)) a) p

embu-round2 : {A : Set} (P : A → Set) (a : A)
             → embu (embu-inv P) a → P a
embu-round2 P a t = coe (app= (embu-fg P) a) t

freeThm : (f : (X : Set) → X → X) (A : Set) (P : A → Set) (a : A) (p : P a) → P (f A a)
freeThm f A P a p = finally where
  w : A ∈ i · Set
  w = embu-inv P
  ww : (i : 𝕀) → Set
  ww i = embu-inv P * i
  pp : (i : 𝕀) → ww i
  pp i = embu-round P a p * i
  app : (i : 𝕀) → ww i
  app i = f (ww i) (pp i)
  makepath : (f A a) ∈ i · ww i
  makepath = lam app
  finally : P (f A a)
  finally = embu-round2 P (f A a) makepath
