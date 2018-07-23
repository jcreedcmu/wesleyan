{-# OPTIONS --without-K --rewriting #-}
module 2018-07-23 where

open import HoTT

postulate
  Tw : Set → Set
  op : Set → Set
  op/involute : {A : Set} → op (op A) ↦ A
  {-# REWRITE op/involute #-}

  dom : {C : Set} → Tw C → C
  cod : {C : Set} → Tw C → (op C)
  Fop : {A B : Set} → (A → B) → (op A) → (op B)
  Fop/involute : {A B : Set} {f : A → B} → Fop (Fop f) ↦ f
  {-# REWRITE Fop/involute #-}

  prod/op : {A B : Set} → (op (A × B)) ↦ (op A) × (op B)
  {-# REWRITE prod/op #-}

  prod/fop : {A B C : Set} {f : A → B × C} → Fop f ↦ λ a → Fop (fst ∘ f) a , Fop (snd ∘ f) a
  {-# REWRITE prod/fop #-}

db : Set → Set
db ℂ = op ℂ × ℂ

postulate
  ℂ 𝔻 𝔼 𝕊 : Set
  t : db ℂ → 𝔻
  u : db ℂ → 𝔼
  A : db ℂ × db 𝔻 → 𝕊
  B : db ℂ × db 𝔼 → 𝕊

πx : Tw (Tw ℂ) → ℂ
πx τ = dom (dom τ)

πy : Tw (Tw ℂ) → op ℂ
πy τ = cod (dom τ)

πd : Tw (Tw ℂ) → op ℂ
πd τ = (Fop dom) (cod τ)

πe : Tw (Tw ℂ) → ℂ
πe τ = (Fop cod) (cod τ)

-- This is the ↓+τ(u) way of doing it
fB : Tw (Tw ℂ) → 𝕊
fB τ = B ((πd τ , πe τ) , (Fop u (πx τ , πy τ) , u (πd τ , πe τ)))

-- This is the ↑+τ(u) way of doing it
fB' : Tw (Tw ℂ) → 𝕊
fB' τ = B ((πd τ , πe τ) , (Fop u (πe τ , πd τ) , u (πy τ , πx τ)))

-- This is the ↓-τ(t) way of doing it
fA : Tw (Tw ℂ) → (op 𝕊)
fA = Fop (λ τ → A ((Fop πe τ , Fop πd τ) ,
     (Fop t (Fop πy τ , Fop πx τ) , t (Fop πe τ , Fop πd τ))))

-- This is the ↑-τ(t) way of doing it
fA' : Tw (Tw ℂ) → (op 𝕊)
fA' = Fop (λ τ → A ((Fop πe τ , Fop πd τ) ,
     (Fop t (Fop πd τ , Fop πe τ) , t (Fop πx τ , Fop πy τ))))
