module Modal where

open import HoTT hiding ( _▹_ )

data Sgn : Set where
  s+ : Sgn
  s- : Sgn

data Lev : Set where
  val : Lev
  tru : Lev

data Prop : Lev → Sgn → Set where
  ↑ : {ℓ : Lev} → Prop ℓ s+ → Prop ℓ s-
  ↓ : {ℓ : Lev} → Prop ℓ s- → Prop ℓ s+
  𝟙 : Prop tru s+
  F : Prop val s+ → Prop tru s+
  U : Prop tru s- → Prop val s-
  _⊸_ : {ℓ : Lev} → Prop ℓ s+ → Prop ℓ s- → Prop ℓ s-

Pos : Set
Pos = Prop tru s+

Neg : Set
Neg = Prop tru s-

postulate
  frame : Set
  kripke : Set
  ≤v : kripke → kripke → Set
  # : kripke → frame → Set

res : Lev → Sgn → Set -- worlds, frames
res ℓ s+ = kripke
res ℓ s- = kripke × frame

-- This is some very domain specific stuff: [
data ≤ : Lev → kripke → kripke → Set where
  /≤t : (α : kripke) → ≤ tru α α
  /≤v : {α β : kripke} → ≤v α β → ≤ val α β

data ⊸R {ℓ : Lev} : res ℓ s+ → res ℓ s- → res ℓ s- → Set where
  /⊸R : (α : kripke) (φ : frame) → ⊸R α (α , φ) (α , φ)

data 𝟙R {ℓ : Lev} : res ℓ s+ → res ℓ s+ → Set where
  /𝟙R : (α : kripke) → 𝟙R α α
-- ]

▹ : (ℓ : Lev) → res ℓ s+ → res ℓ s- → Set
▹ ℓ u (v , φ) = ≤ ℓ u v → # v φ

_⋆_ : {ℓ : Lev} {s : Sgn} → Prop ℓ s → res ℓ s → Set
_⋆_ {ℓ} (↑ p) φ = (α : res ℓ s+) → p ⋆ α → ▹ ℓ α φ
_⋆_ {ℓ} (↓ p) α = (φ : res ℓ s-) → p ⋆ φ → ▹ ℓ α φ
_⋆_ {ℓ} 𝟙 α = Σ (res ℓ s+) (λ α' → 𝟙R {ℓ} α α')
_⋆_ {ℓ} (p ⊸ n) φ = Σ (res ℓ s+ × res ℓ s-) (λ { (α , ψ) → (p ⋆ α) × (n ⋆ ψ) × ⊸R {ℓ} α ψ φ })
(F p) ⋆ α = p ⋆ α
(U n) ⋆ φ = n ⋆ φ


Prov : (p : Pos) → Set
Prov p = (α : kripke) → p ⋆ α

Entail : (p q : Pos) → Set
Entail p q = (α : kripke) → p ⋆ α → q ⋆ α

□ : Neg → Pos
□ n = F (↓ (U n))

postulate
  refl : (β : kripke) → (≤v β β)
  trans0 : {α β γ : kripke} → (≤v α β) → (≤v β γ) → (≤v α γ)

incl : {α β : kripke} → (≤ tru α β) → (≤ val α β)
incl (/≤t α) = /≤v (refl α)

trans : {α β γ : kripke} → (≤ val α β) → (≤ val β γ) → (≤ val α γ)
trans (/≤v R) (/≤v R') = /≤v (trans0 R R')

easyCase : {n : Neg} → Prov (□ (↑ (□ (↑ 𝟙))))
easyCase {n} α (β , φ) k R = k β (λ { (γ , φ') k' R' → k' γ (γ , /𝟙R γ) (/≤t γ)}) (/≤t β)

axiomT : {n : Neg} → Entail (□ n) (↓ n)
axiomT {n} α k (β , φ) pf R = k (β , φ) pf (incl R)

axiom4 : {n : Neg} → Entail (□ n) (□ (↑ (□ n)))
axiom4 α prem (β , φ) conc R = conc β (λ { (γ , φ') pfn R' → prem (γ , φ') pfn (trans R R')}) (/≤t β)

sameThing : {p q : Pos} → Entail p q → Prov (↓ (p ⊸ ↑ q))
sameThing ent α (β , φ) (._ , ppf , k , /⊸R .β .φ) R = k β (ent β ppf) (/≤t β)
