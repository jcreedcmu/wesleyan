open import HoTT
open import Modal
open import ExampleModalTheory as EMT
open import Proofs
open Proofs.TurnCrank (EMT.mt)

-- some abbreviations
Pos = Prop (tru , s+)
Neg = Prop (tru , s-)
Posv = Prop (val , s+)
Negv = Prop (val , s-)

F : Posv → Pos
F pv = C EMT.Opr.F (pv :: nil)

_⊸_ : Pos → Neg → Neg
p ⊸ n = C (EMT.Opr.⊸ tru) (p :: n :: nil)

𝟙 : Pos
𝟙 = C (EMT.Opr.𝟙 tru) nil

U : Neg → Negv
U n = C EMT.Opr.U (n :: nil)

□ : Neg → Pos
□ n = F (↓ (U n))

{- a useful alternative equivalent presentation of the interpretation
function for this particular mode theory -}

module _ where
  open EMT.Opr
  _⋆⋆_ : {μ : Mode} {s : Sgn} → Prop (μ , s) → Res (μ , s) → Set
  _⋆⋆_ {μ} (↑ p) φ = (α : Res (μ , s+)) → p ⋆⋆ α → ▹ μ α φ
  _⋆⋆_ {μ} (↓ p) α = (φ : Res (μ , s-)) → p ⋆⋆ φ → ▹ μ α φ
  (C F (p :: nil)) ⋆⋆ α = p ⋆⋆ α
  (C U (n :: nil)) ⋆⋆ φ = n ⋆⋆ φ
  (C (⊸ μ) (p :: n :: nil)) ⋆⋆ (β , φ) = (p ⋆⋆ β) × (n ⋆⋆ (β , φ))
  (C (𝟙 μ) ps) ⋆⋆ α = Unit

  into : {μs : Signed Mode} → (p : Prop μs) (α : Res μs)
    → p ⋆ α → p ⋆⋆ α
  out : {μs : Signed Mode} → (p : Prop μs) (α : Res μs)
    → p ⋆⋆ α → p ⋆ α
  into (↑ p) φ z α pfp = z α (out p α pfp)
  into (↓ n) α z φ pfn = z φ (out n φ pfn)
  into (C F (p :: nil)) α ((.α :: nil) , /FR .α , z , unit) = into p α z
  into (C U (n :: nil)) (β , φ) ((.(β , φ) :: nil) , /UR .β .φ , z , unit) = into n (β , φ) z
  into (C (⊸ μ) (p :: (n :: nil))) .(β , φ)
    ((β :: (.(β , φ) :: nil)) , /⊸R .μ .β φ , zp , zn , unit) = into p β zp , into n (β , φ) zn
  into (C (𝟙 μ) nil) α z = tt

  out (↑ p) α z φ pfp = z φ (into p φ pfp)
  out (↓ n) φ z α pfn = z α (into n α pfn)
  out (C F (p :: nil)) α  z = (α :: nil) , (/FR α , out p α z , tt)
  out (C U (n :: nil)) (β , φ) z = ((β , φ) :: nil) , (/UR β φ , out n (β , φ) z , tt)
  out (C (⊸ μ) (p :: n :: nil)) (β , φ) (zp , zn) = (β :: (β , φ) :: nil) ,
    /⊸R μ β φ , out p β zp , out n (β , φ) zn , tt
  out (C (𝟙 μ) nil) α tt = nil , ((/𝟙R μ α) , tt)

Prov : (p : Pos) → Set
Prov p = (α : kripke) → p ⋆⋆ α

Entail : (p q : Pos) → Set
Entail p q = (α : kripke) → p ⋆⋆ α → q ⋆⋆ α

-- couple little lemmas
incl : {α β : kripke} → (≤ tru α β) → (≤ val α β)
incl (/≤t α) = /≤v (refl α)

trans : {α β γ : kripke} → (≤ val α β) → (≤ val β γ) → (≤ val α γ)
trans (/≤v R) (/≤v R') = /≤v (trans0 R R')

-- proving some actual propositions
easyCase : {n : Neg} → Prov (□ (↑ (□ (↑ 𝟙))))
easyCase {n} α (β , φ) k R = k β (λ { (γ , φ') k' R' → k' γ tt (/≤t γ)}) (/≤t β)

axiomT : {n : Neg} → Entail (□ n) (↓ n)
axiomT {n} α k (β , φ) pf R = k (β , φ) pf (incl R)

axiom4 : {n : Neg} → Entail (□ n) (□ (↑ (□ n)))
axiom4 α prem (β , φ) conc R = conc β (λ { (γ , φ') pfn R' → prem (γ , φ') pfn (trans R R')}) (/≤t β)

sameThing : {p q : Pos} → Entail p q → Prov (↓ (p ⊸ ↑ q))
sameThing ent α (β , φ) (ppf , k) R = k β (ent β ppf) (/≤t β)
