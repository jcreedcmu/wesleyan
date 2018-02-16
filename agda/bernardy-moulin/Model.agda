{-# OPTIONS --without-K --rewriting #-}
module Model where

open import HoTT hiding ( O; Path; _*_ ; !)

record Category {n} {m} : Set (lmax (lsucc n) (lsucc m)) where
  field
    Obj : Set n
    Mor : Obj → Obj → Set m
    _⋆_ : {A B C : Obj} → Mor B C → Mor A B → Mor A C
    Id : (A : Obj) → Mor A A
    -- Do these with rewriting instead maybe?
    Assoc : {A B C D : Obj} (f : Mor A B) (g : Mor B C) (h : Mor C D) → ((h ⋆ g) ⋆ f) == (h ⋆ (g ⋆ f))
    IdLawL : {A B : Obj} (f : Mor A B) → (Id B ⋆ f) == f
    IdLawR : {A B : Obj} (f : Mor A B) → (f ⋆ Id A) == f
open Category

SetC : ∀ {n} → Category {lsucc n} {n}
SetC {n} = record
             { Obj = Set n
             ; Mor = λ A B → A → B
             ; _⋆_ = λ g f → g ∘ f
             ; Id = λ A x → x
             ; Assoc = λ f g h → idp
             ; IdLawL = λ f → idp
             ; IdLawR = λ f → idp
             }

record Functor {n1} {m1} {n2} {m2} (ℂ : Category {n1} {m1}) (𝔻 : Category {n2} {m2}) : Set (lmax (lmax m1 m2) (lmax n1 n2)) where
  field
    ObjF : ℂ .Obj → 𝔻 .Obj
    MorF : {A B : ℂ .Obj} (f : ℂ .Mor A B) → 𝔻 .Mor (ObjF A) (ObjF B)
    IdLawF : {A : ℂ .Obj} → MorF (ℂ .Id A) == 𝔻 .Id (ObjF A)
    CompLawF : {A B C : ℂ .Obj} (g : ℂ .Mor B C) (f : ℂ .Mor A B) → MorF (ℂ ._⋆_ g f) == 𝔻 ._⋆_ (MorF g) (MorF f)
open Functor

-- PartialInj m n is the set of partial injections from a set of size m to a set of size n.
data PartialInj : ℕ → ℕ → Set where
  pε : {m : ℕ} → PartialInj 0 m
  pπ : {n m : ℕ} → PartialInj n m → PartialInj (S n) m -- project
  pσ : {n m p : ℕ} → p < (S m) → PartialInj n m → PartialInj (S n) (S m) -- select

-- PartialInjEval : {n m p : ℕ} → PartialInj n m → p < n → ℕ
-- PartialInjEval {.0} {m} {p} pε le = {!!}
-- PartialInjEval {.(S _)} {m} {p} (pπ pi) le = {!!}
-- PartialInjEval {.(S _)} {.(S _)} {p} (pσ x pi) le = {!!}

-- PartialInjEvalCorrect : {n m p : ℕ} (pi : PartialInj n m) (le : p < n) → PartialInjEval pi le < m
-- PartialInjEvalCorrect = {!!}
postulate
  XXX : {A : Set} → A

PartialInjComp : {n m p : ℕ} → PartialInj m p → PartialInj n m → PartialInj n p
PartialInjComp {0} {m} {p} g f = pε
PartialInjComp {S n} {m} {p} g f = XXX

∁ : Category {lzero} {lzero}
∁ = record
      { Obj = ℕ
      ; Mor = PartialInj
      ; _⋆_ = PartialInjComp
      ; Id = XXX
      ; Assoc = XXX
      ; IdLawL = XXX
      ; IdLawR = XXX
      }

ModelType : Set₁
ModelType = Functor ∁ (SetC {lzero})


-- Binary Products
MProd : ModelType → ModelType → ModelType
MProd A B = record {
  ObjF = λ C → A .ObjF C × B .ObjF C ;
  MorF = λ { f (a , b) → (A .MorF f a) , (B .MorF f b) } ;
  IdLawF = λ= (λ x → pair×= (app= (A .IdLawF) (fst x)) (app= (B .IdLawF) (snd x))) ;
  CompLawF = XXX
  }
