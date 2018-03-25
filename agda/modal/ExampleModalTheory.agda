open import HoTT
open import ModalDefs

module ExampleModalTheory where

data Mode : Set where
  val : Mode
  tru : Mode
data Opr : Set where
  F U : Opr
  ⊸ : Mode → Opr

postulate
  frame : Set
  kripke : Set
  ≤v : kripke → kripke → Set
  # : kripke → frame → Set

Input : Opr → List (Signed Mode)
Input F = (val , s+) :: nil
Input U = (tru , s-) :: nil
Input (⊸ μ) = (μ , s+) :: (μ , s-) :: nil

Output : Opr → Signed Mode
Output F = (tru , s+)
Output U = (val , s-)
Output (⊸ μ) = (μ , s-)

Res : Signed Mode → Set -- worlds, frames
Res (μ , s+) = kripke
Res (μ , s-) = kripke × frame

mt : ModeTheory
mt = record {
  Mode = Mode ;
  Opr = Opr ;
  Input = Input ;
  Output = Output ;
  Res = Res }
