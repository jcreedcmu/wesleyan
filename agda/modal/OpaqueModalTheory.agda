open import HoTT

module OpaqueModalTheory where

record OpaqueModeTheory : Set₁ where
  field
    -- A set of modes
    Mode : Set
    -- with a notion of what the 'resources' are for that mode
    Res : Mode → Set
    -- and a set of operations (with which to generate the
    -- multiplicative connectives)
    Opr : Set
    -- with specified types
    Input Output : Opr → Mode
    -- and specified resource relations
    Reln : (ω : Opr) → Res (Input ω) → Res (Output ω) → Set
