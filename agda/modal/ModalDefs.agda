module ModalDefs where

open import HoTT hiding ( _▹_ )

-- Kind of like HList except we parametrize by a custom little
-- universe (U, El) of codes of types which works better than levels.
data Mlist {U : Set} (El : U → Set) : List U → Set where
  nil : Mlist El nil
  _::_ : {A : U} {L : List U} → El A → Mlist El L → Mlist El (A :: L)

-- data Mode : Set where
--   val : Mode
--   tru : Mode

data Sgn : Set where
  s+ : Sgn
  s- : Sgn

Signed : Set → Set
Signed T = T × Sgn

record ModeTheory : Set₁ where
  field
    Mode : Set
    Opr : Set
    Input : Opr → List (Signed Mode)
    Output : Opr → Signed Mode
    Res : Signed Mode → Set
