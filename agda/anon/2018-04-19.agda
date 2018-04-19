{-# OPTIONS --without-K --rewriting #-}

module 2018-04-19 where

data Maybe (A : Set) : Set where
  None : Maybe A
  Some : A → Maybe A

open import HoTT hiding ( O ; Span ; All ; S )

postulate
  Cat : Set
  dtype : Cat → Set

Dctx : Set₁
Dctx = List Set

Obj : Dctx → Set
Obj nil = ⊤
Obj (h :: tl) = Maybe h × Obj tl

data Morc {ℂ : Set} : Maybe ℂ → Maybe ℂ → Set where
  idm : {m : Maybe ℂ} → Morc m m
  arm : {c : ℂ} → Morc None (Some c)

Mor : {Δ : Dctx} (δ1 δ2 : Obj Δ) → Set
Mor {nil} δ1 δ2 = ⊤
Mor {ℂ :: Δ} (c1 , δ1) (c2 , δ2) = Morc c1 c2 × Mor δ1 δ2

Comp : {Δ : Dctx} {δ1 δ2 δ3 : Obj Δ} (m : Mor δ1 δ2) (n : Mor δ2 δ3) → Mor δ1 δ3
Comp {nil} {δ1} {δ2} {δ3} m n = tt
Comp {ℂ :: Δ} (idm , ms) (idm , ns) = idm , Comp ms ns
Comp {ℂ :: Δ} (idm , ms) (arm , ns) = arm , Comp ms ns
Comp {ℂ :: Δ} (arm , ms) (idm , ns) = arm , Comp ms ns

Init : (Δ : Dctx) → Obj Δ
Init nil = tt
Init (h :: tl) = None , Init tl

Uniq : (Δ : Dctx) (δ : Obj Δ) → Mor (Init Δ) δ
Uniq nil δ = tt
Uniq (ℂ :: Δ) (None , δ) = idm , Uniq Δ δ
Uniq (ℂ :: Δ) (Some x , δ) = arm , Uniq Δ δ

record Dtype (Δ : Dctx) : Set₁ where
  field
    opart : Obj Δ → Set
    mpart : {δ1 δ2 : Obj Δ} (φ : Mor δ1 δ2) → opart δ1 → opart δ2
    fpart : {δ1 δ2 δ3 : Obj Δ} (φ : Mor δ1 δ2) (ψ : Mor δ2 δ3) → mpart ψ ∘ mpart φ == mpart (Comp φ ψ)
open Dtype

record Dpf {Δ : Dctx} (A : Dtype Δ) : Set where
  field
    opartp : (δ : Obj Δ) → opart A δ
    mpartp : {δ1 δ2 : Obj Δ} (φ : Mor δ1 δ2) → opartp δ2 == mpart A φ (opartp δ1)
open Dpf

applyTo : {Δ : Dctx} (ℂ : Set) → (c : Maybe ℂ) → Dtype (ℂ :: Δ) → Dtype Δ
applyTo ℂ c A = record {
  opart = λ δ → opart A (c , δ) ;
  mpart = λ φ → mpart A (idm , φ) ;
  fpart = λ φ ψ → fpart A (idm , φ) (idm , ψ) }

All : {Δ : Dctx} (ℂ : Set) → Dtype (ℂ :: Δ) → Dtype Δ
All ℂ A = applyTo ℂ None A

_⇒_ : {Δ : Dctx} → Dtype Δ → Dtype Δ → Dtype Δ
_⇒_ {Δ} A B = record {
  opart = λ δ → (δ' : Obj Δ) (m : Mor δ δ') → opart A δ' → opart B δ' ;
  -- this is wrong, for missing the functoriality requirement^
  mpart = λ φ f1 δ' ψ x → f1 δ' (Comp φ ψ) x  ;
  fpart = {!!} }

record Dspan (Δ : Dctx) (N : Set) : Set₁ where
  field
    𝕏 : Dtype Δ
    𝔸 : N → Dtype Δ
    𝕗 : (n : N) → Dpf (𝕏 ⇒ 𝔸 n)
open Dspan

Witness : {Δ : Dctx} {ℂ : Set} → Dspan Δ ℂ → Dtype (ℂ :: Δ)
Witness {Δ} {ℂ} S = record {
  opart = op ;
  mpart = mp ;
  fpart = {!!} } where
  op : Maybe ℂ × Obj Δ → Set
  op (None , δ) = opart (𝕏 S) δ
  op (Some c , δ) = opart (𝔸 S c) δ
  mp : {δ1 δ2 : Maybe ℂ × Obj Δ} →
      Morc (fst δ1) (fst δ2) × Mor (snd δ1) (snd δ2) → op δ1 → op δ2
  mp {None , δ1} {.None , δ2} (idm , φ) xs = mpart (𝕏 S) φ xs
  mp {Some c , δ1} {.(Some c) , δ2} (idm , φ) xs = mpart (𝔸 S c) φ xs
  mp {.None , δ1} {.(Some _) , δ2} (arm {c}, φ) xs = opartp (𝕗 S c) δ1 δ2 φ (mpart (𝕏 S) φ xs)

--   ♯ : ∀ {n} → Set n → Set n
--   η : ∀ {n} {A : Set n} → A → ♯ A
--   push : {A B : Set} → (A → B) → ♯ A → ♯ B
--   pull : ∀ {n} {A B C : Set n} (f : A → B) (g : ♯ A → C) (h : B → C)
--     → ((a : A) → g (η a) == h (f a)) → ♯ B → C
--   coprod : ∀ {n} {A B : Set n} → ♯ (A ⊔ B) → ♯ A ⊔ ♯ B

-- record Span (N : Set) : Set₁ where
--   field
--     ℂ : Set
--     𝔸 : N → Set
--     𝕗 : (n : N) → ℂ → 𝔸 n
-- open Span
