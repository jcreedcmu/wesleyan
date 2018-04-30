{-# OPTIONS --without-K --rewriting #-}
module SegalizationInSimplicialSets where

open import HoTT

data Mono : ℕ → ℕ → Set where
  mzero : (n : ℕ) → Mono O n
  myes : {n m : ℕ} → Mono n m → Mono (S n) (S m)
  mno : {n m : ℕ} → Mono n m → Mono n (S m)

postulate
  sim : ℕ → Set
  hom : {n m : ℕ} → Mono n m == (sim n → sim m)

sinl : sim 0 → sim 1
sinl = coe hom (mzero 1)

sinr : sim 0 → sim 1
sinr = coe hom (mno (mzero O))

Λ : Set
Λ = Pushout (span (sim 1) (sim 1) (sim 0) sinr sinl)

Δ : Set
Δ = sim 2

postulate
  ι : Λ → Δ

module _ {i} where

  postulate  -- HIT
    $ : (X : Set i) → Set i

  module _ {X : Set i} where

    postulate  -- HIT
      inj : X → $ X
      fill : (Λ → $ X) → Δ → $ X
      bound : (ℓ : Λ) (f : Λ → $ X) → fill f (ι ℓ) == f ℓ
      uniq : (t : Δ) (f : Δ → $ X) → fill (f ∘ ι) t == f t

  module $Elim {X : Set i} {l} {P : $ X → Set l}
    (inj* : (x : X) → P (inj x))
    (fill* : (f : Λ → $ X) (δ : Δ) (ih : (ℓ : Λ) → P (f ℓ)) → P (fill f δ))
    (bound* : (ℓ : Λ) (f : Λ → $ X) (ih : (ℓ : Λ) → P (f ℓ))
            → fill* f (ι ℓ) ih == ih ℓ [ P ↓ bound ℓ f ])
    (uniq* : (t : Δ) (f : Δ → $ X) (ih : (t : Δ) → P (f t))
           → fill* (f ∘ ι) t (ih ∘ ι) == ih t [ P ↓ uniq t f ])
    where

    postulate  -- HIT
      elim : Π ($ X) P
      inj-β : ∀ x → elim (inj x) ↦ inj* x
      fill-β : ∀ f δ → elim (fill f δ) ↦ fill* f δ (elim ∘ f)
      {-# REWRITE inj-β #-}
      {-# REWRITE fill-β #-}

    postulate  -- HIT
     bound-β : (ℓ : Λ) (f : Λ → $ X) → apd elim (bound ℓ f) == bound* ℓ f (elim ∘ f)
     uniq-β :  (t : Δ) (f : Δ → $ X) → apd elim (uniq  t f) == uniq*  t f (elim ∘ f)

$-elim = $Elim.elim

Mor : {X : Set} → X → X → Set
Mor {X} x y = Σ (sim 1 → X) (λ f → ((z : sim 0) → f (sinl z) == x) × ((z : sim 0) → f (sinr z) == y))


compWithIota : {X : Set} → (Δ → X) → (Λ → X)
compWithIota {X} f = f ∘ ι

$isSegal : {X : Set} → is-equiv (compWithIota {$ X})
$isSegal {X} = is-eq compWithIota fill (λ f → λ= λ ℓ → bound ℓ f) (λ f → λ= λ t → uniq t f)
