open import HoTT
open import ModalDefs

module TurnCrank (MT : ModeTheory) where
open ModeTheory MT

data Prop : Signed Mode → Set
data Prop where
  ↑ : {μ : Mode} → Prop (μ , s+) → Prop (μ , s-)
  ↓ : {μ : Mode} → Prop (μ , s-) → Prop (μ , s+)
  C : (ω : Opr) → Mlist Prop (Input ω) → Prop (Output ω)

  -- F : Prop val s+ → Prop tru s+
  -- U : Prop tru s- → Prop val s-
  -- _⊸_ : {μ : Mode} → Prop μ s+ → Prop μ s- → Prop μ s-




-- -- This is some very domain specific stuff: [
-- data ≤ : Mode → kripke → kripke → Set where
--   /≤t : (α : kripke) → ≤ tru α α
--   /≤v : {α β : kripke} → ≤v α β → ≤ val α β

-- data ⊸R {μ : Mode} : res μ s+ → res μ s- → res μ s- → Set where
--   /⊸R : (α : kripke) (φ : frame) → ⊸R α (α , φ) (α , φ)

-- data 𝟙R {μ : Mode} : res μ s+ → res μ s+ → Set where
--   /𝟙R : (α : kripke) → 𝟙R α α
-- -- ]

-- ▹ : (μ : Mode) → res μ s+ → res μ s- → Set
-- ▹ μ u (v , φ) = ≤ μ u v → # v φ

-- _⋆_ : {μ : Mode} {s : Sgn} → Prop μ s → res μ s → Set
-- _⋆_ {μ} (↑ p) φ = (α : res μ s+) → p ⋆ α → ▹ μ α φ
-- _⋆_ {μ} (↓ p) α = (φ : res μ s-) → p ⋆ φ → ▹ μ α φ
-- _⋆_ {μ} 𝟙 α = Σ (res μ s+) (λ α' → 𝟙R {μ} α α')
-- _⋆_ {μ} (p ⊸ n) φ = Σ (res μ s+ × res μ s-) (λ { (α , ψ) → (p ⋆ α) × (n ⋆ ψ) × ⊸R {μ} α ψ φ })
-- (F p) ⋆ α = p ⋆ α
-- (U n) ⋆ φ = n ⋆ φ


-- Prov : (p : Pos) → Set
-- Prov p = (α : kripke) → p ⋆ α

-- Entail : (p q : Pos) → Set
-- Entail p q = (α : kripke) → p ⋆ α → q ⋆ α

-- □ : Neg → Pos
-- □ n = F (↓ (U n))

-- postulate
--   refl : (β : kripke) → (≤v β β)
--   trans0 : {α β γ : kripke} → (≤v α β) → (≤v β γ) → (≤v α γ)

-- incl : {α β : kripke} → (≤ tru α β) → (≤ val α β)
-- incl (/≤t α) = /≤v (refl α)

-- trans : {α β γ : kripke} → (≤ val α β) → (≤ val β γ) → (≤ val α γ)
-- trans (/≤v R) (/≤v R') = /≤v (trans0 R R')

-- easyCase : {n : Neg} → Prov (□ (↑ (□ (↑ 𝟙))))
-- easyCase {n} α (β , φ) k R = k β (λ { (γ , φ') k' R' → k' γ (γ , /𝟙R γ) (/≤t γ)}) (/≤t β)

-- axiomT : {n : Neg} → Entail (□ n) (↓ n)
-- axiomT {n} α k (β , φ) pf R = k (β , φ) pf (incl R)

-- axiom4 : {n : Neg} → Entail (□ n) (□ (↑ (□ n)))
-- axiom4 α prem (β , φ) conc R = conc β (λ { (γ , φ') pfn R' → prem (γ , φ') pfn (trans R R')}) (/≤t β)

-- sameThing : {p q : Pos} → Entail p q → Prov (↓ (p ⊸ ↑ q))
-- sameThing ent α (β , φ) (._ , ppf , k , /⊸R .β .φ) R = k β (ent β ppf) (/≤t β)
