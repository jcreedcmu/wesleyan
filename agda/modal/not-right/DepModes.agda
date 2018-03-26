open import HoTT

module DepModes where

-- The two polarities, positive and negative
data Sgn : Set where
  s+ : Sgn
  s- : Sgn

-- Something together with a sign
Signed : Set → Set
Signed T = T × Sgn

-- A mode theory consists of
record ModeTheory : Set₁ where
  constructor MTh
  field
    Ctx : Set -- dependent list of signed modes
    • : Ctx -- empty context
    Mode : Ctx → Set -- modes in context
    _,,_ : (Γ : Ctx) → Signed (Mode Γ) → Ctx -- ctx append
    ManyRes : Ctx → Set  -- resource sets at a context
    Res : {Γ : Ctx} → Signed (Mode Γ) → Set  -- resource sets at a context
    ▹ : {Γ : Ctx} {μ : Mode Γ}
      → Res (μ , s+)
      → Res (μ , s-) → Set
    Opr : Set -- a set of operations
    -- with specified arity:
    Input : Opr → Ctx
    Output : (ω : Opr) → Signed (Mode (Input ω))
    -- and specified resource relations
    Reln : (ω : Opr) → ManyRes (Input ω) → Res (Output ω) → Set
