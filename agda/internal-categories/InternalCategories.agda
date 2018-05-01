{-# OPTIONS --without-K #-}
module InternalCategories where

open import HoTT hiding ( [_] )

record Cat (X : Set) : Set₁ where
  constructor cat
  field
    hom : X → X → Set
    _⋆_ : {x y z : X} → hom x y → hom y z → hom x z
    id : {x : X} → hom x x
    assoc : {x y z w : X} {f : hom x y} {g : hom y z} {h : hom z w}
      → ((f ⋆ g) ⋆ h) == (f ⋆ (g ⋆ h))
open Cat

inj : {X : Set} (F : X → Set) → Cat X
inj {X} F = cat (λ x y → F x → F y) (λ f g → g ∘ f) (λ z → z) idp

postulate
  inj-equiv : {X : Set} → is-equiv (inj {X})

int : {X : Set} (ℂ : Cat X) → (X → Set)
int = inj-equiv .is-equiv.g

round : {X : Set} (ℂ : Cat X) → inj (int ℂ) == ℂ
round = inj-equiv .is-equiv.f-g

roundHom : {X : Set} (ℂ : Cat X) → (λ x y → int ℂ x → int ℂ y) == hom ℂ
roundHom ℂ = ap hom (round ℂ)

[_,_] = int

-- functoriality of [_,_]
fct : {X : Set} {ℂ : Cat X} {c d : X}
  → hom ℂ c d → [ ℂ , c ] → [ ℂ , d ]
fct {X} {ℂ} {c} {d} h = coe (ap (λ z → z c d) (! (roundHom ℂ))) h

isnat : {A B X : Set} {ℂ : Cat X} →
   ((c : X) → ([ ℂ , c ] → A) → ([ ℂ , c ] → B)) → Set
isnat {A} {B} {X} {ℂ} z = (c d : X) (f : hom ℂ c d) (k : [ ℂ , d ] → A)
  → z d k ∘ fct f == z c (k ∘ fct f)

injf : {A B X : Set} {ℂ : Cat X} →
  (A → B) → Σ ((c : X) → ([ ℂ , c ] → A) → ([ ℂ , c ] → B)) isnat
injf f = (λ c g → f ∘ g) , (λ c d f0 k → idp)

postulate
  injf-equiv : {A B X : Set} {ℂ : Cat X} → is-equiv (injf {A} {B} {X} {ℂ})
