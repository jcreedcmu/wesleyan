open import HoTT
open import Modes

module ModalT where

data Mode : Set where
  val : Mode
  tru : Mode

module Opr where
  data Opr : Set where
    F U : Opr
    ⊸ 𝟙 : Mode → Opr
open Opr

postulate
  frame : Set
  kripke : Set
  ≤v : kripke → kripke → Set
  # : kripke → frame → Set

Input : Opr → List (Signed Mode)
Input F = (val , s+) :: nil
Input U = (tru , s-) :: nil
Input (⊸ μ) = (μ , s+) :: (μ , s-) :: nil
Input (𝟙 μ) = nil

Output : Opr → Signed Mode
Output F = (tru , s+)
Output U = (val , s-)
Output (⊸ μ) = (μ , s-)
Output (𝟙 μ) = (μ , s+)

Res : Signed Mode → Set -- worlds, frames
Res (μ , s+) = kripke
Res (μ , s-) = kripke × frame

data Reln : (ω : Opr) → Mlist Res (Input ω) → Res (Output ω) → Set where
  /⊸R : (μ : Mode) (α : kripke) (φ : frame)
      → Reln (⊸ μ) (α :: (α , φ) :: nil) (α , φ)
  /𝟙R : (μ : Mode) (α : kripke)
      → Reln (𝟙 μ) nil α
  /FR : (α : kripke) → Reln F (α :: nil) α
  /UR : (β : kripke) (φ : frame) → Reln U ((β , φ) :: nil) (β , φ)

data ≤ : Mode → kripke → kripke → Set where
  /≤t : (α : kripke) → ≤ tru α α
  /≤v : {α β : kripke} → ≤v α β → ≤ val α β

▹ : (μ : Mode) → Res (μ , s+) → Res (μ , s-) → Set
▹ μ u (v , φ) = ≤ μ u v → # v φ

postulate
  refl : (β : kripke) → (≤v β β)
  trans0 : {α β γ : kripke} → (≤v α β) → (≤v β γ) → (≤v α γ)

mt : ModeTheory
mt = record {
  Mode = Mode ;
  Opr = Opr ;
  Input = Input ;
  Output = Output ;
  Res = Res ;
  ▹ = ▹ ;
  Reln = Reln}
