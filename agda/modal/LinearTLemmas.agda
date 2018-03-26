open import HoTT renaming ( ! to rev )
open import Modes
open import LinearT as MT
open import Proofs
open Proofs.TurnCrank (MT.mt) using ( Prop ; pft )
open Prop
open ProofTheory pft using ( _⋆_ )

-- some abbreviations
Pos = Prop (res , s+)
Neg = Prop (res , s-)
Posv = Prop (tru , s+)
Negv = Prop (tru , s-)

F : Posv → Pos
F pv = C MT.Opr.F (pv :: nil)

_⊸_ : Pos → Neg → Neg
p ⊸ n = C MT.Opr.⊸ (p :: n :: nil)

𝟙 : Pos
𝟙 = C MT.Opr.𝟙 nil

U : Neg → Negv
U n = C MT.Opr.U (n :: nil)

! : Neg → Pos
! n = F (↓ (U n))

{- a useful alternative equivalent presentation of the interpretation
function for this particular mode theory -}

module _ where
  open MT.Opr
  _⋆⋆_ : {μ : Mode} {s : Sgn} → Prop (μ , s) → Res (μ , s) → Set
  ↑ p ⋆⋆ φ = (α : Res (_ , s+)) → p ⋆⋆ α → ▹ _ α φ
  ↓ n ⋆⋆ α = (φ : Res (_ , s-)) → n ⋆⋆ φ → ▹ _ α φ
  C F (p :: nil) ⋆⋆ α = (p ⋆⋆ tt) × (α == a𝟙)
  C U (n :: nil) ⋆⋆ φ = Σ frame (λ φ' → (n ⋆⋆ φ') × (aU φ' == φ))
  C ⊸ (p :: n :: nil) ⋆⋆ φ = Σ (world × frame)
      (λ { (α , φ') → (p ⋆⋆ α) × (n ⋆⋆ φ') × (φ == a⊸ α φ')})
  C 𝟙 nil ⋆⋆ α = α == a𝟙
  C ⊗ (p₁ :: p₂ :: nil) ⋆⋆ α = Σ (world × world)
      (λ { (α₁ , α₂) → (p₁ ⋆⋆ α₁) × (p₂ ⋆⋆ α₂) × (α == a⊗ α₁ α₂)})

  into : {μs : Signed Mode} → (p : Prop μs) (α : Res μs)
    → p ⋆ α → p ⋆⋆ α
  out : {μs : Signed Mode} → (p : Prop μs) (α : Res μs)
    → p ⋆⋆ α → p ⋆ α
  into (↑ p) φ z α pfp = z α (out p α pfp)
  into (↓ n) α z φ pfn = z φ (out n φ pfn)
  into (TurnCrank.C Opr.F (p :: nil)) .a𝟙 (.(unit :: nil) , (z , unit) , /FR) =
    into p tt z , idp
  into (TurnCrank.C Opr.U (n :: nil)) .(aU φ) ((φ :: nil) , (z , unit) , /UR .φ) =
    φ , into n φ z , idp
  into (TurnCrank.C ⊸ (p :: (n :: nil))) .(a⊸ α φ) (.(α :: (φ :: nil)) , (zp , zn , tt) , /⊸R α φ) =
    (α , φ) , into p α zp , into n φ zn , idp
  into (TurnCrank.C ⊗ (p1 :: (p2 :: nil))) .(a⊗ α1 α2) (.(α1 :: (α2 :: nil)) , (z1 , z2 , tt) , /⊗R α1 α2) =
    (α1 , α2) , into p1 α1 z1 , into p2 α2 z2 , idp
  into (TurnCrank.C 𝟙 nil) .a𝟙 (.nil , tt , /𝟙R) = idp

  out (↑ p) α z φ pfp = z φ (into p φ pfp)
  out (↓ n) φ z α pfn = z α (into n α pfn)
  out (TurnCrank.C Opr.F (p :: nil)) .a𝟙 (z , idp) = (unit :: nil) , (out p tt z , unit) , /FR
  out (TurnCrank.C Opr.U (n :: nil)) .(aU φ) (φ , z , idp) = (φ :: nil) , (((out n φ z) , unit) , (/UR φ))
  out (TurnCrank.C ⊸ (p :: (n :: nil))) .(a⊸ α φ) ((α , φ) , zp , zn , idp) =
      (α :: φ :: nil) , ((out p α zp , (out n φ zn , unit)) , (/⊸R α φ))
  out (TurnCrank.C ⊗ (p1 :: (p2 :: nil))) .(a⊗ α1 α2) ((α1 , α2) , z1 , z2 , idp) =
      (α1 :: α2 :: nil) , ((out p1 α1 z1 , (out p2 α2 z2 , unit)) , (/⊗R α1 α2))
  out (TurnCrank.C 𝟙 nil) .(a𝟙) idp =
      nil , (unit , /𝟙R)

Prov : (p : Pos) → Set
Prov p = p ⋆⋆ a𝟙

easyCase : {n : Neg} → Prov (↓ ((↓ n) ⊸ n))
easyCase {n} .(a⊸ α' φ') ((α' , φ') , npf , npf' , idp) = done where
  almost : ▹res α' φ'
  almost = npf φ' npf'

  almost2 : ▹res (a⊗ a𝟙 α') φ'
  almost2 = transport (λ x → ▹res x φ') (rev (unitlaw α')) almost

  done : ▹res a𝟙 (a⊸ α' φ')
  done = –> (adjoint a𝟙 α' φ') almost2
