{-# OPTIONS --without-K --rewriting #-}
module CategoryVariables where

open import HoTT hiding (_∙_ )

postulate
  {- elements of Del are category-variable contexts Δ. I'm just going
     to work top-down, postulating the existence of this and digging
     down and postulating whatever properies I need of it as I need
     them. -}
  Del : Set

module del (Δ : Del) where
  postulate

    {- The category ⟪Δ⟫ -}
    Obj1 : Set
    Mor1 : Obj1 → Obj1 → Set
    id1 : (c : Obj1) → Mor1 c c
    _∙1_  : {c d e : Obj1} (g : Mor1 d e) (f : Mor1 c d) → Mor1 c e

    {- some rerwites for id laws and associativity -}
    idr-rewrite : {c d : Obj1} (f : Mor1 c d) → (f ∙1 (id1 c)) ↦ f
    idl-rewrite : {c d : Obj1} (f : Mor1 c d) → ((id1 d) ∙1 f) ↦ f
    assoc-rewrite : {b c d e : Obj1} (m3 : Mor1 b c) (m2 : Mor1 c d) (m1 : Mor1 d e)  →
      (m1 ∙1 (m2 ∙1 m3)) ↦ ((m1 ∙1 m2) ∙1 m3)
  {-# REWRITE idr-rewrite idl-rewrite assoc-rewrite #-}

  {- The category ⟦Δ⟧ = ⟪Δ⟫ × ⟪Δ⟫^op -}
  Obj : Set
  Obj = Obj1 × Obj1

  Mor : Obj → Obj → Set
  Mor (d , d') (e , e') = Mor1 d e × Mor1 e' d'

  idm : (δ : Obj) → Mor δ δ
  idm (d , d') = (id1 d , id1 d')

  infixl 20 _∙_
  _∙_  : {γ δ ε : Obj} (ψ : Mor δ ε) (φ : Mor γ δ) → Mor γ ε
  (ψ1 , ψ2) ∙ (φ1 , φ2) = (ψ1 ∙1 φ1) , (φ2 ∙1 ψ2)

  {- Dualization of objects in ⟦Δ⟧ -}
  ~ : Obj → Obj
  ~ (d , d') = (d' , d)

  {- Dualization of morphisms in ⟦Δ⟧ -}
  ~m : {δ ε : Obj} → Mor δ ε → Mor (~ ε) (~ δ)
  ~m (f , f') = (f' , f)

  {- A morphism of 𝕋(Δ), the twisted arrow category of ⟦Δ⟧ -}
  data Tor {δ' ε' δ ε} : Mor δ' ε' → Mor δ ε → Set where
    tor : (τ1 : Mor δ' δ) (φ : Mor δ ε) (τ2 : Mor ε ε') → Tor (τ2 ∙ φ ∙ τ1) φ

  {- Identity arrows in 𝕋(Δ) -}
  idt : ∀ {δ ε} (φ : Mor δ ε) → Tor φ φ
  idt {δ} {ε} φ = tor (idm δ) φ (idm ε)

  {- Some more useful things we can do in 𝕋(Δ) -}
  module Tw {δ ε δ' ε' : Obj} {ψ : Mor δ' ε'} {φ : Mor δ ε} where
    _∙t_ : ∀ {δ'' ε''} {ζ : Mor δ'' ε''} → Tor ψ φ → Tor ζ ψ → Tor ζ φ
    (tor τ1 _ τ2) ∙t (tor σ1 _ σ2) = tor (τ1 ∙ σ1) _ (σ2 ∙ τ2)

    ~t : Tor ψ φ → Tor (~m ψ) (~m φ)
    ~t (tor τ1 φ τ2) = tor (~m τ2) (~m φ) (~m τ1)

    L :  (Tor ψ φ) → Mor δ' δ
    L (tor ℓ _ _) = ℓ

    R :  (Tor ψ φ) → Mor ε ε'
    R (tor _ _ r) = r

    ◅ : (τ : Tor ψ φ) → Tor ψ (L τ)
    ◅ (tor τ1 .φ τ2) = tor (idm δ') τ1 (τ2 ∙ φ)

    ▻ : (τ : Tor ψ φ) → Tor ψ (R τ)
    ▻ (tor τ1 .φ τ2) = tor (φ ∙ τ1) τ2 (idm ε')

  open Tw public

  {- 'swing' operators special-cased to identity arrows -}
  ◅i : ∀ {δ ε} (φ : Mor δ ε) → Tor φ (idm δ)
  ◅i {δ} {ε} φ = ◅ (idt φ)

  ▻i : ∀ {δ ε} (φ : Mor δ ε) → Tor φ (idm ε)
  ▻i {δ} {ε} φ = ▻ (idt φ)

module FixDel (Δ : Del) where
  open del Δ

  {- A rather big mutual recursion starts now... -}
  {- ---------------------------------------------}

  {- There is a type of contexts which we will actually define as a datatype -}
  data Ctx : Set

  {- We assume the existence of types indexed by their context -}
  postulate
    Tp : (Γ : Ctx) → Set

  {- Contexts can be empty, dual, or of the form Γ, x + A -}
  data Ctx where
    ctx/· : Ctx
    ctx/op : Ctx → Ctx
    _:+_ : (Γ : Ctx) (A : Tp Γ) → Ctx

  {- Declare the functions that compute semantics of contexts. Since
     an object of 𝕋(Δ) is a morphism of ⟦Δ⟧, the 'object part' of Γ's
     meaning takes a Mor, and the 'morphism part' takes a Tor. -}

  ctx/mor : ∀ {δ ε} (Γ : Ctx) (φ : Mor δ ε) → Set
  ctx/tor : ∀ {δ ε δ' ε'} {φ : Mor δ ε} {ψ : Mor δ' ε'}
          (Γ : Ctx) (τ : Tor ψ φ) →
          ctx/mor Γ ψ → ctx/mor Γ φ


  postulate
    {- The meaning of ctx is a functor from 𝕋(Δ) → Set -}
    ctx/tor/comp : ∀ {δ ε δ' ε' δ'' ε''} {φ : Mor δ ε} {φ' : Mor δ' ε'} {φ'' : Mor δ'' ε''} →
      (Γ : Ctx) (τ : Tor φ' φ) (σ : Tor φ'' φ') (g : ctx/mor Γ φ'')
      → ctx/tor Γ τ (ctx/tor Γ σ g) ↦ ctx/tor Γ (τ ∙t σ) g
    ctx/tor/id : ∀ {δ ε} {φ : Mor δ ε} →
      (Γ : Ctx)  (g : ctx/mor Γ φ)
      → ctx/tor Γ (idt φ) g ↦ g
    {-# REWRITE ctx/tor/comp ctx/tor/id #-}

    {- Here's what we assume we can extract from the meanings of types -}
    tp/obj : {Γ : Ctx} (A : Tp Γ) (δ : Obj) → ctx/mor Γ (idm δ) → Set
    tp/mor : {Γ : Ctx} (A : Tp Γ) {δ ε : Obj} (φ : Mor δ ε) →
           (g : ctx/mor Γ φ) → tp/obj A δ (ctx/tor Γ (◅i φ) g) → tp/obj A ε (ctx/tor Γ (▻i φ) g)

  {- The 'object part' ('static part') of the meaning of contexts -}
  ctx/mor ctx/· φ = ⊤
  ctx/mor (ctx/op Γ) φ = ctx/mor Γ (~m φ)
  ctx/mor {δ} {ε} (Γ :+ A) φ = Σ (ctx/mor Γ φ) (λ g → tp/obj A δ (ctx/tor Γ (◅i φ) g))

  {- The 'morphism part' ('dynamic part') of the meaning of contexts -}
  ctx/tor ctx/· τ tt = tt
  ctx/tor (ctx/op Γ) τ = ctx/tor Γ (~t τ)
  -- This @-pattern is required to make the functoriality rewrite trigger
  ctx/tor {δ} {ε} {δ'} {ε'} {φ} {ψ} (Γ :+ A) τ@(tor _ _ _) (g , a) =
    (ctx/tor Γ τ g) , (tp/mor A (L τ) (ctx/tor Γ (◅ τ) g) a)

  {- Types can be dualized -}
  postulate
    tp/op : {Γ : Ctx} → Tp Γ → Tp (ctx/op Γ)

  {- Here's how to make Γ, x - A -}
  _:-_ : (Γ : Ctx) → Tp Γ → Ctx
  Γ :- A = ctx/op (ctx/op Γ :+ tp/op A)
