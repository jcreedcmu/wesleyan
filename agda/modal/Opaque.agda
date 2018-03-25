open import HoTT

-- There are two simplification goals of this file:
-- (a) Forget that the positive and negative aspects of a mode are special,
-- and think of them as merely two different modes
-- (b) Limit ourselves to unary operations, such that the lost
-- generality can be recovered by defining tensor products in the mode theory.

-- The two Postures, multiplicative and shift-like
data Post : Set where
  mult : Post
  shft : Post

module Opaque where

record OpaqueModeTheory : Set₁ where
  field
    -- A set of modes
    Mode : Set
    -- with a notion of what the 'resources' are for that mode
    Res : Mode → Set
    -- and a set of operations
    Opr : Post → Set
    -- with specified types
    Input Output : {π : Post} → Opr π → Mode
    -- and specified resource relations
    Reln : {π : Post} (ω : Opr π) → Res (Input ω) → Res (Output ω) → Set

record ProofTheory (MT : OpaqueModeTheory) : Set₁ where
  open OpaqueModeTheory MT
  field
    -- A set of props
    Prop : Mode → Set
    -- with an interpretation function
    _⋆_ : {μs : Mode} → Prop μs → Res μs → Set
