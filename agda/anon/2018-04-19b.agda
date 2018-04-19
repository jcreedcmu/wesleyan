{-# OPTIONS --without-K --rewriting #-}

module 2018-04-19b where

data Maybe (A : Set) : Set where
  None : Maybe A
  Some : A → Maybe A

open import HoTT hiding ( O ; Span ; All ; S ; Empty)

record Cat (n m : ULevel) : Set (lsucc (lmax n m)) where
  constructor cat
  field
    Obj : Set n
    Mor : Obj → Obj → Set m
    Comp : ∀ {A B C} (f : Mor A B) (g : Mor B C) → Mor A C
    Zero : Obj
    Bang : (c : Obj) → Mor Zero c

prodCat : ∀ {n1 m1 n2 m2} → Cat n1 m1 → Cat n2 m2 → Cat (lmax n1 n2) (lmax m1 m2)
prodCat
  (cat Obj1 Mor1 Comp1 Zero1 Bang1)
  (cat Obj2 Mor2 Comp2 Zero2 Bang2) =
  cat
    (Obj1 × Obj2)
    (λ { (a1 , a2) (b1 , b2) → Mor1 a1 b1 × Mor2 a2 b2 })
    (λ { (f1 , f2) (g1 , g2) → Comp1 f1 g1 , Comp2 f2 g2})
    (Zero1 , Zero2)
    ((λ { (c1 , c2) → (Bang1 c1) , (Bang2 c2)} ))

unitCat : Cat _ _
unitCat =
  cat ⊤
    (λ { tt tt → ⊤ })
    (λ { tt tt → tt })
    tt
    (λ { tt → tt })

data Spmor {ℂ : Set} : Maybe ℂ → Maybe ℂ → Set where
  idm : {m : Maybe ℂ} → Spmor m m
  arm : {c : ℂ} → Spmor None (Some c)

Spcomp : {ℂ : Set} {δ1 δ2 δ3 : Maybe ℂ} (m : Spmor δ1 δ2) (n : Spmor δ2 δ3) → Spmor δ1 δ3
Spcomp idm idm = idm
Spcomp idm arm = arm
Spcomp arm idm = arm

Spbang : {ℂ : Set} (c : Maybe ℂ) → Spmor None c
Spbang None = idm
Spbang (Some _) = arm

spanCat : (ℂ : Set) → Cat _ _
spanCat ℂ =
  cat (Maybe ℂ) Spmor Spcomp None Spbang


data Empty {n} : Set n where

abort : ∀ {n} (A : Set n) → Empty {n} → A
abort A ()

setCat : ∀ {n} → Cat (lsucc n) n
setCat {n} = cat (Set n) (λ X Y → X → Y) (λ f g → g ∘ f) Empty abort

record Functor {n1 m1 n2 m2} (ℂ : Cat n1 m1) (𝔻 : Cat n2 m2) :
       Set (lmax (lmax n1 m1) (lmax n2 m2)) where
  open Cat
  field
    oF : Obj ℂ → Obj 𝔻
    mF : {C1 C2 : Obj ℂ} → Mor ℂ C1 C2 → Mor 𝔻 (oF C1) (oF C2)
    fF : {C1 C2 C3 : Obj ℂ} (f : Mor ℂ C1 C2) (g : Mor ℂ C2 C3)
      → mF (Comp ℂ f g) == Comp 𝔻 (mF f) (mF g)

Dtype : ∀ {n m p} (Δ : Cat n m) → Set (lmax (lsucc p) (lmax m n))
Dtype {n} {m} {p} Δ = Functor Δ (setCat {p})

-- record Dpf {Δ : Dctx} (A : Dtype Δ) : Set where
--   field
--     opartp : (δ : Obj Δ) → opart A δ
--     mpartp : {δ1 δ2 : Obj Δ} (φ : Mor δ1 δ2) → opartp δ2 == mpart A φ (opartp δ1)
-- open Dpf

-- applyTo : {Δ : Dctx} (ℂ : Set) → (c : Maybe ℂ) → Dtype (ℂ :: Δ) → Dtype Δ
-- applyTo ℂ c A = record {
--   opart = λ δ → opart A (c , δ) ;
--   mpart = λ φ → mpart A (idm , φ) ;
--   fpart = λ φ ψ → fpart A (idm , φ) (idm , ψ) }

-- All : {Δ : Dctx} (ℂ : Set) → Dtype (ℂ :: Δ) → Dtype Δ
-- All ℂ A = applyTo ℂ None A

-- _⇒_ : {Δ : Dctx} → Dtype Δ → Dtype Δ → Dtype Δ
-- _⇒_ {Δ} A B = record {
--   opart = λ δ → (δ' : Obj Δ) (m : Mor δ δ') → opart A δ' → opart B δ' ;
--   -- this is wrong, for missing the functoriality requirement^
--   mpart = λ φ f1 δ' ψ x → f1 δ' (Comp φ ψ) x  ;
--   fpart = {!!} }

-- record Dspan (Δ : Dctx) (N : Set) : Set₁ where
--   field
--     𝕏 : Dtype Δ
--     𝔸 : N → Dtype Δ
--     𝕗 : (n : N) → Dpf (𝕏 ⇒ 𝔸 n)
-- open Dspan

-- Witness : {Δ : Dctx} {ℂ : Set} → Dspan Δ ℂ → Dtype (ℂ :: Δ)
-- Witness {Δ} {ℂ} S = record {
--   opart = op ;
--   mpart = mp ;
--   fpart = {!!} } where
--   op : Maybe ℂ × Obj Δ → Set
--   op (None , δ) = opart (𝕏 S) δ
--   op (Some c , δ) = opart (𝔸 S c) δ
--   mp : {δ1 δ2 : Maybe ℂ × Obj Δ} →
--       Morc (fst δ1) (fst δ2) × Mor (snd δ1) (snd δ2) → op δ1 → op δ2
--   mp {None , δ1} {.None , δ2} (idm , φ) xs = mpart (𝕏 S) φ xs
--   mp {Some c , δ1} {.(Some c) , δ2} (idm , φ) xs = mpart (𝔸 S c) φ xs
--   mp {.None , δ1} {.(Some _) , δ2} (arm {c}, φ) xs = opartp (𝕗 S c) δ1 δ2 φ (mpart (𝕏 S) φ xs)

-- --   ♯ : ∀ {n} → Set n → Set n
-- --   η : ∀ {n} {A : Set n} → A → ♯ A
-- --   push : {A B : Set} → (A → B) → ♯ A → ♯ B
-- --   pull : ∀ {n} {A B C : Set n} (f : A → B) (g : ♯ A → C) (h : B → C)
-- --     → ((a : A) → g (η a) == h (f a)) → ♯ B → C
-- --   coprod : ∀ {n} {A B : Set n} → ♯ (A ⊔ B) → ♯ A ⊔ ♯ B

-- -- record Span (N : Set) : Set₁ where
-- --   field
-- --     ℂ : Set
-- --     𝔸 : N → Set
-- --     𝕗 : (n : N) → ℂ → 𝔸 n
-- -- open Span
