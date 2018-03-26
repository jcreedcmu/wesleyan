open import HoTT
open import Modes

module LinearT where

data Mode : Set where
  res : Mode
  tru : Mode

module Opr where
  data Opr : Set where
    F U : Opr
    ⊸ 𝟙 ⊗ : Opr
open Opr

postulate
  frame : Set
  tframe : Set
  world : Set
  a𝟙 : world
  a⊗ : world → world → world
  a⊸ : world → frame → frame
  aU : frame → tframe
  ▹res : world → frame → Set
  # : tframe → Set

Input : Opr → List (Signed Mode)
Input F = (tru , s+) :: nil
Input U = (res , s-) :: nil
Input ⊸ = (res , s+) :: (res , s-) :: nil
Input ⊗ = (res , s+) :: (res , s+) :: nil
Input 𝟙 = nil

Output : Opr → Signed Mode
Output F = (res , s+)
Output U = (tru , s-)
Output ⊸ = (res , s-)
Output ⊗ = (res , s+)
Output 𝟙 = (res , s+)

Res : Signed Mode → Set -- worlds, frames
Res (res , s+) = world
Res (res , s-) = frame
Res (tru , s+) = Unit
Res (tru , s-) = tframe

data Reln : (ω : Opr) → Mlist Res (Input ω) → Res (Output ω) → Set where
  /⊸R : (α : world) (φ : frame) → Reln ⊸ (α :: φ :: nil) (a⊸ α φ)
  /⊗R : (α β : world) → Reln ⊗ (α :: β :: nil) (a⊗ α β)
  /𝟙R : Reln 𝟙 nil a𝟙
  /FR : Reln F (tt :: nil) a𝟙
  /UR : (φ : frame) → Reln U (φ :: nil) (aU φ)

▹ : (μ : Mode) → Res (μ , s+) → Res (μ , s-) → Set
▹ res α φ = ▹res α φ
▹ tru tt φ = # φ

mt : ModeTheory
mt = record {
  Mode = Mode ;
  Opr = Opr ;
  Input = Input ;
  Output = Output ;
  Res = Res ;
  ▹ = ▹ ;
  Reln = Reln}
