{-# OPTIONS --without-K --rewriting #-}

module 2018-04-24 where

open import HoTT hiding ( O ; Span ; Path )

postulate
  # : Set → Set
  -- # is a functor:
  #F : {A B : Set} → (A → B) → # A → # B

  ι : {n : Set} → n → # n
  -- ι is a natural transformation:
  ιnat-law : {A B : Set} (f : A → B) (a : A) → #F f (ι a) ↦ ι (f a)
  {-# REWRITE ιnat-law #-}

  Path : (n : Set) (A : Set) → (n → A) → Set -- # n → A with specified endpoints
  app : {n : Set} {A : Set} {ε : n → A} → Path n A ε → # n → A

  app-β-law : {n : Set} {A : Set} {ε : n → A} (π : Path n A ε) (k : n)
            → app π (ι k) ↦ ε k
  {-# REWRITE app-β-law #-}

  lam : {n : Set} {A : Set} (f : # n → A) → Path n A (λ k → f (ι k))

push : {m n : Set} {A : Set} {ε : n → A} (g : m → n) → Path n A ε → Path m A (ε ∘ g)
push g π = lam (λ x → app π (#F g x))

data 𝟙 : Set where -- walking binary relation
  • : 𝟙

postulate
  Path1 : ∀ {ℓ} (A : Set ℓ) → A → Set ℓ -- # 1 → A with specified endpoint
  app1 : ∀ {ℓ} {A : Set ℓ} {a : A} → Path1 A a → # 𝟙 → A

  app1-β-law-• : ∀ {ℓ} {n : Set} {A : Set ℓ} {a : A} (π : Path1 A a) → app1 π (ι •) ↦ a
  {-# REWRITE app1-β-law-• #-}

  lam1 : ∀ {ℓ} {A : Set ℓ} (f : # 𝟙 → A) → Path1 A (f (ι •))

data 𝟚 : Set where -- walking binary relation
  dom cod : 𝟚

postulate
  Path2 : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ -- # 2 → A with specified endpoints
  app2 : ∀ {ℓ} {A : Set ℓ} {a b : A} → Path2 A a b → # 𝟚 → A

  app2-β-law-dom : ∀ {ℓ} {A : Set ℓ} {a b : A} (π : Path2 A a b) → app2 π (ι dom) ↦ a
  app2-β-law-cod : ∀ {ℓ} {A : Set ℓ} {a b : A} (π : Path2 A a b) → app2 π (ι cod) ↦ b
  {-# REWRITE app2-β-law-dom #-}
  {-# REWRITE app2-β-law-cod #-}

  lam2 : ∀ {ℓ} {A : Set ℓ} (f : # 𝟚 → A) → Path2 A (f (ι dom)) (f (ι cod))

inj : 𝟚 → 𝟙 → 𝟚
inj x • = x


pdom : {A : Set} {a b : A} → Path2 A a b → Path1 A a
pdom π = lam1 (λ x → app2 π (#F (inj dom) x))

pcod : {A : Set} {a b : A} → Path2 A a b → Path1 A b
pcod π = lam1 (λ x → app2 π (#F (inj cod) x))

-- should be equiv to isDir:
isDirAlt : {A : Set} {a b : A} (π : Path2 A a b) → Set
isDirAlt {A} {a} {b} π = pdom π == lam1 (λ _ → a)

isDir : {A : Set} {a b : A} (π : Path2 A a b) → Set
isDir {A} {a} {b} π = (x : # 𝟙) → app2 π (#F (inj dom) x) == a

Mor : {A : Set} → A → A → Set -- directed # 2 → A with specified endpoints
Mor {A} a b = Σ (Path2 A a b) isDir

isAdj : {ℂ 𝔻 : Set} (F : ℂ → 𝔻) (U : 𝔻 → ℂ) → Set
isAdj {ℂ} {𝔻} F U = (c : ℂ) (d : 𝔻) → Mor (F c) d ≃ Mor c (U d)


data holds {ℂ ℂ' : Set} (hom : Path2 Set ℂ ℂ') : (c : ℂ) (c' : ℂ') → Set where
   /holds : (q : (ν : # 𝟚) → app2 hom ν) → holds hom (q (ι dom)) (q (ι cod))

isAdj2 : {ℂF 𝔻U ℂU 𝔻F : Set} (HomC : Path2 Set ℂF ℂU) (HomD : Path2 Set 𝔻F 𝔻U)
        (F : ℂF → 𝔻F) (U : 𝔻U → ℂU) → Set
isAdj2 {ℂF} {𝔻U} HomC HomD F U =
      (c : ℂF) (d : 𝔻U) → holds HomD (F c) d ≃ holds HomC c (U d)
