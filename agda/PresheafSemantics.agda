{-# OPTIONS --without-K --rewriting #-}

module PresheafSemantics where

open import HoTT

postulate
  Cat : Set
  obj : Cat → Set
  mor : {ℂ : Cat} → obj ℂ → obj ℂ → Set

data Ctxd : Set where
  dempty : Ctxd
  dext : Ctxd → (ℂ : Cat) → Ctxd

postulate
  Ctx : Ctxd → Set
  Tp : {Δ : Ctxd} → Ctx Δ → Set
  Tm : {Δ : Ctxd} {Γ : Ctx Δ} → Tp Γ → Set
  ext : {Δ : Ctxd} (Γ : Ctx Δ) → Tp Γ → Ctx Δ
  dw : {Δ : Ctxd} {ℂ : Cat} → Ctx Δ → Ctx (dext Δ ℂ)
  w : {Δ : Ctxd} {Γ : Ctx Δ} (A : Tp Γ) → Tp Γ → Tp (ext Γ A)

Obj : Ctxd → Set
Obj dempty = ⊤
Obj (dext Δ ℂ) = Obj Δ × obj ℂ

Mor : (Δ : Ctxd) → Obj Δ → Obj Δ → Set
Mor dempty tt tt = ⊤
Mor (dext Δ ℂ) (δ1 , c) (δ2 , d) = Mor Δ δ1 δ2 × mor c d

-- These are the induction hypotheses I assume of all the types that
-- otherwise exist in the type system.
postulate
  iCtxObj : {Δ : Ctxd} (Γ : Ctx Δ)
    → Obj Δ → Set
  iCtxMor : {Δ : Ctxd} (Γ : Ctx Δ)
    → {δ1 δ2 : Obj Δ} (φ : Mor Δ δ1 δ2)
    → iCtxObj Γ δ1 → iCtxObj Γ δ2
  iTpObj : {Δ : Ctxd} {Γ : Ctx Δ} (A : Tp Γ)
    → (δ : Obj Δ) → iCtxObj Γ δ → Set
  iTpMor : {Δ : Ctxd} {Γ : Ctx Δ} (A : Tp Γ)
    → {δ1 δ2 : Obj Δ} (φ : Mor Δ δ1 δ2)
    → (γ : iCtxObj Γ δ1) → iTpObj A δ1 γ → iTpObj A δ2 (iCtxMor Γ φ γ)
  iTmObj : {Δ : Ctxd} {Γ : Ctx Δ} {A : Tp Γ} (M : Tm A)
    → (δ : Obj Δ) (γ : iCtxObj Γ δ) → iTpObj A δ γ
  iTmMor : {Δ : Ctxd} {Γ : Ctx Δ} {A : Tp Γ} (M : Tm A)
    → {δ1 δ2 : Obj Δ} (φ : Mor Δ δ1 δ2)
    → (γ : iCtxObj Γ δ1) → iTpMor A φ γ (iTmObj M δ1 γ) == iTmObj M δ2 (iCtxMor Γ φ γ)

-- Here are the 'representable' types that I have codes for, for which
-- I will prove the induction hypothesis incrementally.
data Rtp : {Δ : Ctxd} → Ctx Δ → Set where
  Witness : {Δ : Ctxd} {δ : Obj Δ} {ℂ : Cat} {Γ : Ctx Δ}
    → (A : (c : obj ℂ) → Tp Γ)
    → ({c d : obj ℂ} (f : mor c d) → Tm {Γ = ext Γ (A c)} (w (A c) (A d)))
    → Rtp {dext Δ ℂ} (dw Γ)


postulate
  iCtxObj/dw-rewrite : {Δ : Ctxd} {Γ : Ctx Δ} {δ : Obj Δ} {ℂ : Cat} {c : obj ℂ}
    → iCtxObj (dw Γ) (δ , c) ↦ iCtxObj Γ δ
  {-# REWRITE iCtxObj/dw-rewrite #-}
  iCtxObj/ext-rewrite : {Δ : Ctxd} {Γ : Ctx Δ} {δ : Obj Δ} {A : Tp Γ}
    → iCtxObj (ext Γ A) δ ↦ Σ (iCtxObj Γ δ) (λ γ → iTpObj A δ γ)
  {-# REWRITE iCtxObj/ext-rewrite #-}

rTpObj : {Δ : Ctxd} {Γ : Ctx Δ} (A : Rtp Γ)
  → (δ : Obj Δ) → iCtxObj Γ δ → Set
rTpObj (Witness A _) (δ , c) γ = iTpObj (A c) δ γ

rTpMor : {Δ : Ctxd} {Γ : Ctx Δ} (A : Rtp Γ)
    → {δ1 δ2 : Obj Δ} (φ : Mor Δ δ1 δ2)
    → (γ : iCtxObj Γ δ1) → rTpObj A δ1 γ → rTpObj A δ2 (iCtxMor Γ φ γ)
rTpMor (Witness A M) {δ1 , c} {δ2 , d} (φ , f) γ x = {!iTmObj (M f) δ1 (γ , x)!}
