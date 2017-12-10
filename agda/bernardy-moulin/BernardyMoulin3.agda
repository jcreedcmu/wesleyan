{-# OPTIONS --without-K --rewriting #-}
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

_//_ : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ) (a : A) → p * O
p // a = coe (p .snd) a

embu : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ) (a : A) → Set ℓ
embu {ℓ} {A} p a = (p // a) ∈ i · (p * i)

postulate
  embu-equiv : ∀ {ℓ} {A : Set ℓ} → is-equiv (embu {ℓ} {A})

embu-inv : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → A ∈ i · Set ℓ
embu-inv {ℓ} {A} = embu-equiv .is-equiv.g

embu-fg : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) → embu (embu-inv P) == P
embu-fg {ℓ} {A} = embu-equiv .is-equiv.f-g

embf : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ} {f : (x : A O) → B O x}
  → (f ∈ i · Π (A i) (B i)) → ((x : (i : 𝕀) → A i) → f (x O) ∈ i · B i (x i))
embf p x = (λ i → (p * i) (x i)) , (app= (p .snd) (x O))

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
  wwO : A == ww O
  wwO = embu-inv P .snd
  atzero : (embu-inv P // (f A a)) == app O
  atzero = {!!}
  makepath : (embu-inv P // (f A a)) ∈ i · ww i
  makepath = app , atzero
  finally : P (f A a)
  finally = embu-round2 P (f A a) makepath
