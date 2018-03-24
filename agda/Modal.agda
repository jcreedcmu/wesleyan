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
  F : Prop val s+ → Prop tru s+
  U : Prop tru s- → Prop val s-

postulate
  frame : Set
  kripke : Set
  𝕌 : kripke
  ≤ : kripke → kripke → Set
  # : frame → Set

res : Lev → Sgn → Set -- worlds, frames
res tru s+ = kripke
res tru s- = kripke × frame
res val s+ = Unit
res val s- = frame

▹ : (ℓ : Lev) → res ℓ s+ → res ℓ s- → Set
▹ tru u (v , φ) = ≤ u v → # φ
▹ val tt φ = # φ

postulate
  a-s : res tru s- → Set -- 'semantics' of a-

interp : {ℓ : Lev} {s : Sgn} → Prop ℓ s → res ℓ s → Set
interp {ℓ} (↑ p) φ = (α : res ℓ s+) → interp p α → ▹ ℓ α φ
interp {ℓ} (↓ p) α = (φ : res ℓ s-) → interp p φ → ▹ ℓ α φ
interp (F p) _ = interp p tt
interp (U p) φ = interp p (𝕌 , φ)

Pos : Set
Pos = Prop tru s+

Neg : Set
Neg = Prop tru s-

Entail : (p : Pos) (n : Neg) → Set
Entail p n = (α β : kripke) (φ : frame)
  → interp p β → interp n (β , φ) → ≤ α β → # φ

□ : Neg → Pos
□ n = F (↓ (U n))

postulate
  refl : (β : kripke) → (≤ β β)
  𝕌global : {β : kripke} → (≤ β 𝕌)

ismono : Neg → Set
ismono n = {α β : kripke} {φ : frame} → (≤ α β) → interp n (α , φ) → interp n (β , φ)

axiomT : {n : Neg} → ismono n → Entail (□ n) n
axiomT mon α β φ ppf npf acc = ppf φ {!!}

-- axiom4 : {n : Neg} → Entail (□ n) (↑ (□ (↑ (□ n))))
-- axiom4 α β φ ppf cpf acc = cpf α (λ { (γ , φ') k →
--   λ acc' → k γ (λ { (δ , φ'') →
--     λ npf acc'' → ppf (δ , φ'') npf {!!} }) (refl tru γ) }) acc


-- {--

-- · ⊢ [↓(P ⊸ N)]
-- · ⊢ ↓(P ⊸ N) @ α
-- (P ⊸ N) @ (β, φ), α ≤ β ⊢ #(φ)
-- P @ β, N @ (β, φ), α ≤ β ⊢ #(φ)

-- --}
