module ModalDefs where

open import HoTT hiding ( _▹_ )

-- Kind of like HList except we parametrize by a custom little
-- universe (U, El) of codes of types which works better than levels.
data Mlist {U : Set} (El : U → Set) : List U → Set where
  nil : Mlist El nil
  _::_ : {A : U} {L : List U} → El A → Mlist El L → Mlist El (A :: L)

-- The two polarities, positive and negative
data Sgn : Set where
  s+ : Sgn
  s- : Sgn

-- Something together with a sign
Signed : Set → Set
Signed T = T × Sgn

-- A mode theory consists of
record ModeTheory : Set₁ where
  field
    -- A set of modes
    Mode : Set
    -- with a notion of what the 'resources' are for that mode
    Res : Signed Mode → Set
    -- and a notion of 'consequence' at each mode
    ▹ : (μ : Mode) → Res (μ , s+) → Res (μ , s-) → Set

    -- Also, a set of operations (with which to generate the
    -- multiplicative connectives)
    Opr : Set
    -- with specified arity
    Input : Opr → List (Signed Mode)
    Output : Opr → Signed Mode
    -- and specified resource relations
    Reln : (ω : Opr) → Mlist Res (Input ω) → Res (Output ω) → Set
