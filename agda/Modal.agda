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
  kripke : Sgn → Set
  ≤ : Lev → kripke s+ → kripke s- → Set
  # : frame → Set
  ~ : Lev → kripke s+ → kripke s- → Set

res : Lev → Sgn → Set -- worlds, frames
res ℓ s+ = kripke s+
res ℓ s- = kripke s- × frame

▹ : (ℓ : Lev) → res ℓ s+ → res ℓ s- → Set
▹ ℓ u (v , φ) = ≤ ℓ u v → # φ

data ⊸rel {ℓ : Lev} : res ℓ s+ → res ℓ s- → res ℓ s- → Set where
  same : {α : kripke s+} {φ : res ℓ s- } → ~ ℓ α (φ .fst) → ⊸rel α φ φ

interp : {ℓ : Lev} {s : Sgn} → Prop ℓ s → res ℓ s → Set
interp {ℓ} (↑ p) φ = (α : res ℓ s+) → interp p α → ▹ ℓ α φ
interp {ℓ} (↓ p) α = (φ : res ℓ s-) → interp p φ → ▹ ℓ α φ
interp 𝟙 α = Unit
interp (F p) α = interp p α
interp (U p) φ = interp p φ
interp {ℓ} (p ⊸ n) φ =
  Σ (res ℓ s+ × res ℓ s-) decomp where
  decomp : kripke s+ × kripke s- × frame → Set
  decomp (α , φ') = interp p α × interp n φ' × ⊸rel {ℓ} α φ' φ


Prov : (p : Pos) → Set
Prov p = (α : kripke s+) → interp p α

□ : Neg → Pos
□ n = F (↓ (U n))

-- postulate
--  refl : (ℓ : Lev) (β : kripke) → (≤ ℓ β β)
--  incl : {α β : kripke} → (≤ tru α β) → (≤ val α β)

-- easyCase : {n : Neg} → Prov (↓ (□ □ 1))
-- easyCase {n} α (β , φ) ((α' , _) , prem , conc , same σ) R = prem (β , φ) conc {!!}

axiomT : {n : Neg} → Prov (↓ (□ n ⊸ n))
axiomT {n} α (β , φ) ((α' , _) , prem , conc , same σ) R = prem (β , φ) conc {!!}

axiom4 : {n : Neg} → Prov (↓ (□ n ⊸ ↑ (□ (↑ (□ n)))))
axiom4 α (β , φ) ((α' , _) , prem , conc , same σ) R =
  conc α' (λ { (β' , φ') k R' → k {!!} {!!} {!!} }) {!!}
--  conc α (λ { (β' , φ') k R' → k {!!} {!!} {!!} }) R


-- Goal: (φ₁ : kripke s- × frame) →
--       ((α₁ : kripke s+) →
--        ((φ₂ : kripke s- × frame) → interp .n φ₂ → ▹ val α₁ φ₂) →
--        ▹ tru α₁ φ₁) →
--       ▹ val α φ₁


-- cpf α (λ { (γ , φ') k →
--   λ acc' → k γ (λ { (δ , φ'') →
--     λ npf acc'' → ppf (δ , φ'') npf {!!} }) (refl tru γ) }) acc


-- {--

-- · ⊢ [↓(P ⊸ N)]
-- · ⊢ ↓(P ⊸ N) @ α
-- (P ⊸ N) @ (β, φ), α ≤ β ⊢ #(φ)
-- P @ β, N @ (β, φ), α ≤ β ⊢ #(φ)

-- --}
