{-# OPTIONS --without-K --rewriting #-}
module 2018-05-26 where

open import HoTT hiding (_∙_ )

postulate
  Del : Set

module del (Δ : Del) where
  postulate
    Obj1 : Set
    Mor1 : Obj1 → Obj1 → Set
    id1 : (c : Obj1) → Mor1 c c
    _∙1_  : {c d e : Obj1} (g : Mor1 d e) (f : Mor1 c d) → Mor1 c e

  Obj : Set
  Obj = Obj1 × Obj1

  Mor : Obj → Obj → Set
  Mor (d , d') (e , e') = Mor1 d e × Mor1 e' d'

  idm : (δ : Obj) → Mor δ δ
  idm (d , d') = (id1 d , id1 d')

  infixl 20 _∙_
  _∙_  : {γ δ ε : Obj} (ψ : Mor δ ε) (φ : Mor γ δ) → Mor γ ε
  (ψ1 , ψ2) ∙ (φ1 , φ2) = (ψ1 ∙1 φ1) , (φ2 ∙1 ψ2)

  postulate
    idr-rewrite : {c d : Obj1} (f : Mor1 c d) → (f ∙1 (id1 c)) ↦ f
    idl-rewrite : {c d : Obj1} (f : Mor1 c d) → ((id1 d) ∙1 f) ↦ f
    assoc-rewrite : {b c d e : Obj1} (m3 : Mor1 b c) (m2 : Mor1 c d) (m1 : Mor1 d e)  →
      (m1 ∙1 (m2 ∙1 m3)) ↦ ((m1 ∙1 m2) ∙1 m3)

  {-# REWRITE idr-rewrite idl-rewrite assoc-rewrite #-}

  data Tor {δ' ε' δ ε} : Mor δ' ε' → Mor δ ε → Set where
    tor : (τ1 : Mor δ' δ) (φ : Mor δ ε) (τ2 : Mor ε ε') → Tor (τ2 ∙ φ ∙ τ1) φ

  ~ : Obj → Obj
  ~ (d , d') = (d' , d)

  ~m : {δ ε : Obj} → Mor δ ε → Mor (~ ε) (~ δ)
  ~m (f , f') = (f' , f)

  tlift : ∀ {δ ε} (φ : Mor δ ε) → Tor φ φ
  tlift {δ} {ε} φ = tor (idm δ) φ (idm ε)

  module Tw {δ ε δ' ε' : Obj} {ψ : Mor δ' ε'} {φ : Mor δ ε} where
    ~t : Tor ψ φ → Tor (~m ψ) (~m φ)
    ~t (tor τ1 φ τ2) = tor (~m τ2) (~m φ) (~m τ1)

    L :  (Tor ψ φ) → Mor δ' δ
    L (tor ℓ _ _) = ℓ

    R :  (Tor ψ φ) → Mor ε ε'
    R (tor _ _ r) = r

    ◅t : (τ : Tor ψ φ) → Tor ψ (L τ)
    ◅t (tor τ1 .φ τ2) = tor (idm δ') τ1 (τ2 ∙ φ)

    ▻t : (τ : Tor ψ φ) → Tor ψ (R τ)
    ▻t (tor τ1 .φ τ2) = tor (φ ∙ τ1) τ2 (idm ε')

  open Tw public

  ◅ : ∀ {δ ε} (φ : Mor δ ε) → Tor φ (idm δ)
  ◅ {δ} {ε} φ = ◅t (tlift φ)

  ▻ : ∀ {δ ε} (φ : Mor δ ε) → Tor φ (idm ε)
  ▻ {δ} {ε} φ = ▻t (tlift φ)

module Stuff (Δ : Del) where
  open del Δ

  data Ctx : Set

  postulate
    Tp : (Γ : Ctx) → Set

  data Ctx where
    ctx/· : Ctx
    ctx/op : Ctx → Ctx
    _:+_ : (Γ : Ctx) (A : Tp Γ) → Ctx


  postulate
    tp/op : {Γ : Ctx} → Tp Γ → Tp (ctx/op Γ)

  _:-_ : (Γ : Ctx) → Tp Γ → Ctx
  Γ :- A = ctx/op (ctx/op Γ :+ tp/op A)

  ctx/mor : ∀ {δ ε} (Γ : Ctx) (φ : Mor δ ε) → Set
  ctx/tor : ∀ {δ ε δ' ε'} {φ : Mor δ ε} {ψ : Mor δ' ε'}
          (Γ : Ctx) (τ : Tor ψ φ) →
          ctx/mor Γ ψ → ctx/mor Γ φ

  postulate

    tp/obj : {Γ : Ctx} (A : Tp Γ) (δ : Obj) → ctx/mor Γ (idm δ) → Set
    tp/mor : {Γ : Ctx} (A : Tp Γ) {δ ε : Obj} (φ : Mor δ ε) →
           (g : ctx/mor Γ φ) → tp/obj A δ (ctx/tor Γ (◅ φ) g) → tp/obj A ε (ctx/tor Γ (▻ φ) g)

  ctx/mor ctx/· φ = ⊤
  ctx/mor (ctx/op Γ) φ = ctx/mor Γ (~m φ)
  ctx/mor {δ} {ε} (Γ :+ A) φ = Σ (ctx/mor Γ φ) (λ g → tp/obj A δ (ctx/tor Γ (◅ φ) g))

  ctx/tor ctx/· τ tt = tt
  ctx/tor (ctx/op Γ) τ = ctx/tor Γ (~t τ)
  ctx/tor (Γ :+ A) τ (g , a) = (ctx/tor Γ τ g) , {!!}
