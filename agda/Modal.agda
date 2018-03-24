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
  ≤ : Lev → kripke → kripke → Set
  # : frame → Set

res : Lev → Sgn → Set -- worlds, frames
res ℓ s+ = kripke
res ℓ s- = kripke × frame

▹ : (ℓ : Lev) → res ℓ s+ → res ℓ s- → Set
▹ ℓ u (v , φ) = ≤ ℓ u v → # φ

interp : {ℓ : Lev} {s : Sgn} → Prop ℓ s → res ℓ s → Set
interp {ℓ} (↑ p) φ = (α : res ℓ s+) → interp p α → ▹ ℓ α φ
interp {ℓ} (↓ p) α = (φ : res ℓ s-) → interp p φ → ▹ ℓ α φ
interp (F p) α = interp p α
interp (U p) φ = interp p φ

Pos : Set
Pos = Prop tru s+

Neg : Set
Neg = Prop tru s-

Entail : (p : Pos) (n : Neg) → Set
Entail p n = (α β : kripke) (φ : frame)
  → interp p β → interp n (β , φ) → ≤ tru α β → # φ

□ : Neg → Pos
□ n = F (↓ (U n))

postulate
  refl : (ℓ : Lev) (β : kripke) → (≤ ℓ β β)
  incl : {α β : kripke} → (≤ tru α β) → (≤ val α β)


axiomT : {n : Neg} → Entail (□ n) n
axiomT α β φ ppf npf acc = ppf (β , φ) npf (refl val β)

axiom4 : {n : Neg} → Entail (□ n) (↑ (□ (↑ (□ n))))
axiom4 α β φ ppf cpf acc = cpf α (λ { (γ , φ') k →
  λ acc' → k γ (λ { (δ , φ'') →
    λ npf acc'' → ppf (δ , φ'') npf {!!} }) (refl tru γ) }) acc


{--

· ⊢ [↓(P ⊸ N)]
· ⊢ ↓(P ⊸ N) @ α
(P ⊸ N) @ (β, φ), α ≤ β ⊢ #(φ)
P @ β, N @ (β, φ), α ≤ β ⊢ #(φ)

--}
