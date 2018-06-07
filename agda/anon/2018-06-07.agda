{-# OPTIONS --without-K --rewriting #-}
open import HoTT hiding ( _≤_ ; _∙_ )

module 2018-06-07 where

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

postulate
  Ao : Obj → Set
  Am : {δ ε : Obj} → Mor δ ε → Ao δ → Ao ε

  Bo : (δ : Obj) → Ao δ → Ao (~ δ) → Set
  Bm : {δ ε : Obj} (φ : Mor δ ε) (a : Ao δ) (a* : Ao (~ ε))
    → Bo δ a (Am (~m φ) a*) → Bo ε (Am φ a) a*

  Co : (δ : Obj) (a : Ao δ) (a* : Ao (~ δ))
     (b : Bo δ a a*) (b* : Bo (~ δ) a* a) → Set
  Cm : {δ ε : Obj} (φ : Mor δ ε)
     (a : Ao δ) (a* : Ao (~ ε))
     (b : Bo δ a (Am (~m φ) a*)) (b* : Bo (~ ε) a* (Am φ a))
     → Co δ a (Am (~m φ) a*) b (Bm (~m φ) a* a b*)
     → Co ε (Am φ a) a* (Bm φ a a* b) b*

  Do : (δ : Obj) (a : Ao δ) (a* : Ao (~ δ))
     (b : Bo δ a a*) (b* : Bo (~ δ) a* a)
     (c : Co δ a a* b b*) (c* : Co (~ δ) a* a b* b) → Set
  Dm : {δ ε : Obj} (φ : Mor δ ε)
     (a : Ao δ) (a* : Ao (~ ε))
     (b : Bo δ a (Am (~m φ) a*)) (b* : Bo (~ ε) a* (Am φ a))
     (c : Co δ a (Am (~m φ) a*) b (Bm (~m φ) a* a b*))
     (c* : Co (~ ε) a* (Am φ a) b* (Bm φ a a* b))
     → Do δ a (Am (~m φ) a*) b (Bm (~m φ) a* a b*) c (Cm (~m φ) a* a b* b c*)
     → Do ε (Am φ a) a* (Bm φ a a* b) b* (Cm φ a a* b b* c) c*
