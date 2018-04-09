{-# OPTIONS --without-K --rewriting #-}

module PresheafSemantics where

open import HoTT

postulate
  Cat : Set
  obj : Cat → Set
  mor : {ℂ : Cat} → obj ℂ → obj ℂ → Set
  i0 : (ℂ : Cat) → obj ℂ
  uniq : {ℂ : Cat} (c : obj ℂ) → mor (i0 ℂ) c
  idm : {ℂ : Cat} (c : obj ℂ) → mor c c

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

Idm : (Δ : Ctxd) (δ : Obj Δ) → Mor Δ δ δ
Idm dempty unit = unit
Idm (dext Δ ℂ) (δ , c) = (Idm Δ δ) , (idm c)

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

postulate
  -- rewrite iCtxObj when the context is a Δ-weakened Γ
  iCtxObj/dw-rewrite : {Δ : Ctxd} {Γ : Ctx Δ} {δ : Obj Δ} {ℂ : Cat} {c : obj ℂ}
    → iCtxObj (dw Γ) (δ , c) ↦ iCtxObj Γ δ
  {-# REWRITE iCtxObj/dw-rewrite #-}

  -- rewrite iCtxMor when the context is a Δ-weakened Γ
  iCtxMor/dw-rewrite : {Δ : Ctxd} {Γ : Ctx Δ}
    {δ1 δ2 : Obj Δ} {φ : Mor Δ δ1 δ2} {γ : iCtxObj Γ δ1}
    {ℂ : Cat} {c d : obj ℂ} {f : mor c d}
    → iCtxMor (dw Γ) (φ , f) γ  ↦ iCtxMor Γ φ γ
  {-# REWRITE iCtxMor/dw-rewrite #-}

  -- rewrite iCtxObj when the context has a variable
  iCtxObj/ext-rewrite : {Δ : Ctxd} {Γ : Ctx Δ} {δ : Obj Δ} {A : Tp Γ}
    → iCtxObj (ext Γ A) δ ↦ Σ (iCtxObj Γ δ) (λ γ → iTpObj A δ γ)
  {-# REWRITE iCtxObj/ext-rewrite #-}

  -- rewrite iCtxMor when the morphism is an identity
  iCtxMor/id-rewrite : {Δ : Ctxd} {Γ : Ctx Δ}
    {δ : Obj Δ} {γ : iCtxObj Γ δ}
    → iCtxMor Γ (Idm Δ δ) γ  ↦ γ
  {-# REWRITE iCtxMor/id-rewrite #-}

-- Here are the 'representable' types that I have codes for, for which
-- I will prove the induction hypothesis incrementally.
data Rtp : {Δ : Ctxd} → Ctx Δ → Set where
  Witness : {Δ : Ctxd} {δ : Obj Δ} {ℂ : Cat} {Γ : Ctx Δ}
    → (A : (c : obj ℂ) → Tp Γ)
    → ({c d : obj ℂ} (f : mor c d) → Tm {Γ = ext Γ (A c)} (w (A c) (A d)))
    → Rtp {dext Δ ℂ} (dw Γ)
  Forall : {Δ : Ctxd} {ℂ : Cat} {Γ : Ctx Δ}
    → Tp {dext Δ ℂ} (dw Γ)
    → Rtp {Δ} Γ

postulate
  coeTp : {Δ : Ctxd} {Γ : Ctx Δ} → Rtp Γ → Tp Γ

-- same for terms
data Rtm : {Δ : Ctxd} {Γ : Ctx Δ} → Tp Γ → Set where
  forallIntro : {Δ : Ctxd} {ℂ : Cat} {Γ : Ctx Δ} {A : Tp (dw Γ)}
    → Tm {dext Δ ℂ} {dw Γ} A
    → Rtm {Δ} {Γ} (coeTp (Forall A))
  forallElim : {Δ : Ctxd} {ℂ : Cat} {Γ : Ctx Δ} {A : Tp (dw Γ)}
    → Tm {Δ} {Γ} (coeTp (Forall A))
    → Rtm {dext Δ ℂ} {dw Γ} A

-- proving some theorems
rTpObj : {Δ : Ctxd} {Γ : Ctx Δ} (A : Rtp Γ)
  → (δ : Obj Δ) → iCtxObj Γ δ → Set
rTpObj (Witness A _) (δ , c) γ = iTpObj (A c) δ γ
rTpObj (Forall A) δ γ = iTpObj A (δ , i0 _) γ

rTpMor : {Δ : Ctxd} {Γ : Ctx Δ} (A : Rtp Γ)
    → {δ1 δ2 : Obj Δ} (φ : Mor Δ δ1 δ2)
    → (γ : iCtxObj Γ δ1) → rTpObj A δ1 γ → rTpObj A δ2 (iCtxMor Γ φ γ)
rTpMor (Witness A M) {δ1 , c} {δ2 , d} (φ , f) γ x = {!iTmObj (M f) δ1 (γ , x)!}
rTpMor (Forall A) φ γ x = {!!}

postulate
  coeTp-rewrite : {Δ : Ctxd} {Γ : Ctx Δ} {δ : Obj Δ} {A : Rtp Γ} {γ : iCtxObj Γ δ}
    → iTpObj (coeTp A) δ γ ↦ rTpObj A δ γ
  {-# REWRITE coeTp-rewrite #-}

rTmObj : {Δ : Ctxd} {Γ : Ctx Δ} {A : Tp Γ} (M : Rtm A)
    → (δ : Obj Δ) (γ : iCtxObj Γ δ) → iTpObj A δ γ
rTmObj {Δ} {Γ} {.(coeTp (Forall _))} (forallIntro {ℂ = ℂ} {A = A} M) δ γ =
  iTmObj {dext Δ ℂ} {dw Γ} {A} M (δ , i0 _) γ
rTmObj {.(dext _ _)} {.(dw _)} {A} (forallElim {Δ} {ℂ} {Γ} M) (δ , c) γ =
  iTpMor {dext Δ ℂ} {dw Γ} A {δ , i0 _} {δ , c} (Idm Δ δ , uniq c) γ half where
  half : iTpObj A (δ , i0 _) γ
  half = iTmObj M δ γ
