{-# OPTIONS --without-K #-}

open import HoTT
open import Modes
import Opaque
import Proofs

module OpaqueFromRegular where

module cvtUtil (MT : ModeTheory) where
  open Opaque
  open ModeTheory MT

  OMode : Set
  OMode = Signed Mode

  ORes : OMode → Set
  ORes μs = Res μs

  data OOpr : Post → Set where
    ↑ ↓ : Mode → OOpr shft
    from : Opr → OOpr mult

  OInput : {π : Post} → OOpr π → List OMode
  OInput (↑ μ) = (μ , s+) :: nil
  OInput (↓ μ) = (μ , s-) :: nil
  OInput (from x) = Input x

  OOutput : {π : Post} → OOpr π → OMode
  OOutput (↑ μ) = (μ , s-)
  OOutput (↓ μ) = (μ , s+)
  OOutput (from x) = Output x

  OReln : {π : Post} (ω : OOpr π)
    → Mlist ORes (OInput ω) → ORes (OOutput ω) → Set
  OReln (↑ μ) (α :: nil) φ = ▹ μ α φ
  OReln (↓ μ) (φ :: nil) α = ▹ μ α φ
  OReln (from ω) ℓ α = Reln ω ℓ α

module cvt (MT : ModeTheory) where
  open Opaque
  OMT : OpaqueModeTheory
  OMT =
    OMTh OMode ORes OOpr OInput OOutput OReln where open cvtUtil MT

  open ModeTheory MT

  open Proofs.TurnCrank using () renaming ( Prop to Prop )
  open Opaque.TurnCrank using () renaming ( Prop to OProp )
  open cvtUtil MT

  cvtProp : {μ : Mode} {s : Sgn} → Prop MT (μ , s) → OProp OMT (μ , s)
  cvtProp (Prop.↑ {μ} p) = OProp.C (↑ μ) ((cvtProp p) :: nil)
  cvtProp (Prop.↓ {μ} p) = OProp.C (↓ μ) ((cvtProp p) :: nil)
  cvtProp (Prop.C ω x) = OProp.C (from ω) {!!}
