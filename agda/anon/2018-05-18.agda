{-# OPTIONS --without-K --rewriting #-}
module 2018-05-18 where

open import HoTT

postulate
  Cat : Set
  Obj : Cat → Set
  Mor : {Δ : Cat} → Obj Δ → Obj Δ → Set
  dop : Cat → Cat
  pTp : Cat → Set
  dop/idem : ∀ {Δ} → dop (dop Δ) ↦ Δ
  {-# REWRITE dop/idem #-}
  dop/obj : ∀ {Δ} → Obj (dop Δ) ↦ Obj Δ
  {-# REWRITE dop/obj #-}
  dop/mor : ∀ {Δ} → Mor {dop Δ} ↦ (λ a b → Mor {Δ} b a)
  {-# REWRITE dop/mor #-}

data pCtx : Cat → Set where
  • : ∀ {Δ} → pCtx Δ
  _e+_ : ∀ {Δ} → pCtx Δ → pTp Δ → pCtx Δ
  _e-_ : ∀ {Δ} → pCtx Δ  → pTp (dop Δ) → pCtx Δ

postulate
  wfTp : (Δ : Cat) → pCtx Δ → pTp Δ → Set

cop : ∀ {Δ} → pCtx Δ → pCtx (dop Δ)
cop • = •
cop (Γ e+ A) = (cop Γ) e- A
cop (Γ e- A) = (cop Γ) e+ A

copIdem : ∀ {Δ} → (Γ : pCtx Δ) → Γ == cop (cop Γ)
copIdem • = idp
copIdem (Γ e+ A) = ap (_e+ A) (copIdem Γ)
copIdem (Γ e- A) = ap (_e- A) (copIdem Γ)

postulate
  cop/idem : ∀ {Δ Γ} → cop {Δ} (cop {dop Δ} Γ) ↦ Γ
  {-# REWRITE cop/idem #-}

data wfCtx : (Δ : Cat) → pCtx Δ → Set where
  wfCtx/• : ∀ {Δ} → wfCtx Δ •
  wfCtx/+ : ∀ {Δ Γ A} → wfCtx Δ Γ → wfTp Δ Γ A → wfCtx Δ (Γ e+ A)
  wfCtx/- : ∀ {Δ Γ A} → wfCtx Δ Γ → wfTp (dop Δ) (cop Γ) A → wfCtx Δ (Γ e- A)

wfCtxLem : (Δ : Cat) (Γ : pCtx Δ) → wfCtx Δ Γ → wfCtx (dop Δ) (cop Γ)
wfCtxLem Δ .• wfCtx/• = wfCtx/•
wfCtxLem Δ (Γ e+ A) (wfCtx/+ wfc wft) = wfCtx/- (wfCtxLem Δ Γ wfc) (transport (λ z → wfTp Δ z A) (copIdem Γ) wft)
wfCtxLem Δ (Γ e- A) (wfCtx/- wfc wft) = wfCtx/+ (wfCtxLem Δ Γ wfc) wft

ctxOb : ∀ {Δ Γ} (wΓ : wfCtx Δ Γ) (δ : Obj Δ) → Set

postulate
  tpOb : ∀ {Δ Γ A} {wΓ : wfCtx Δ Γ} (wA : wfTp Δ Γ A) (δ : Obj Δ) (γ : ctxOb wΓ δ) → Set

ctxOb wfCtx/• δ = ⊤
ctxOb (wfCtx/+ wΓ A) δ = Σ (ctxOb wΓ δ) (tpOb {wΓ = wΓ} A δ)
ctxOb {Δ} {Γ e- A} (wfCtx/- wΓ wA) δ = Σ (ctxOb wΓ δ) (λ γ → tpOb {wΓ = wfCtxLem Δ Γ wΓ} wA δ {!!})
