{-# OPTIONS --without-K #-}
module InternalCategories where

open import HoTT hiding ( [_] ; S )

-- should probably have some kind of more stringent size restriction,
-- I think. Possibly finiteness.
record Cat (X : Set) : Set₁ where
  constructor cat
  field
    hom : X → X → Set
    _⋆_ : {x y z : X} → hom x y → hom y z → hom x z
    id : {x : X} → hom x x
    assoc : {x y z w : X} {f : hom x y} {g : hom y z} {h : hom z w}
      → ((f ⋆ g) ⋆ h) == (f ⋆ (g ⋆ h))

Hom = Cat.hom

cay : {X : Set} (F : X → Set) → Cat X
cay {X} F = cat (λ x y → F x → F y) (λ f g → g ∘ f) (λ z → z) idp

-- The 'Cayley axiom': every category is the concrete category of
-- *all* functions among some X-indexed family of sets F : X → Set.
-- What this is doing is essentially postulating into existence the
-- more exotic types that have the specified homs.
postulate
  cay-equiv : {X : Set} → is-equiv (cay {X})

-- Given a category and an object of it, yields that newly
-- representable type.
int : {X : Set} (ℂ : Cat X) → (X → Set)
int = cay-equiv .is-equiv.g

round : {X : Set} (ℂ : Cat X) → cay (int ℂ) == ℂ
round = cay-equiv .is-equiv.f-g

roundHom : {X : Set} (ℂ : Cat X) → (λ x y → int ℂ x → int ℂ y) == Hom ℂ
roundHom ℂ = ap Hom (round ℂ)

extractId : {X : Set} (x : X) (ℂ : Cat X) →
    (λ x → x) == (Cat.id ℂ) [ (λ z → Cat.hom z x x) ↓ round ℂ ]
extractId x ℂ = apd (λ c → Cat.id c {x}) (round ℂ)

roundHom2 : {X : Set} (x y : X) (ℂ : Cat X) → (int ℂ x → int ℂ y) == Hom ℂ x y
roundHom2 x y ℂ = ap (λ z → Hom z x y) (round ℂ)

funcOfMor : {X : Set} {x y : X} {ℂ : Cat X} → Hom ℂ x y → int ℂ x → int ℂ y
funcOfMor {X} {x} {y} {ℂ} = coe (! (roundHom2 x y ℂ))

module lemmaMod {X : Set} (ℂ : Cat X) where
  open Cat ℂ
  ⋆lemma : {x y z : X} (g : hom z y) (f : hom y x) →
      funcOfMor {ℂ = ℂ} (g ⋆ f) == (funcOfMor f) ∘ (funcOfMor g)
  ⋆lemma = {!!}

  generalizeIdLemma : ∀ {n} (x : X) {Catish : Set n} {ℂ 𝔻 : Catish} (p : 𝔻 == ℂ)
    {hom : Catish → Set} {cc : hom ℂ} {dd : hom 𝔻}
    → dd == cc [ hom ↓ p ]
    → coe (! (ap hom p)) cc == dd
  generalizeIdLemma x idp idp = idp

  idlemma : {x : X} → funcOfMor {ℂ = ℂ} (id {x}) == (λ x → x)
  idlemma {x} = generalizeIdLemma x (round ℂ) (extractId x ℂ)
open lemmaMod using ( idlemma )

[_,_] = int

-- This was my first thought for what else might be fruitful to
-- postulate, as of 2017.12.12.
module First where
  -- functoriality of [_,_]
  fct : {X : Set} {ℂ : Cat X} {c d : X}
    → Hom ℂ c d → [ ℂ , c ] → [ ℂ , d ]
  fct {X} {ℂ} {c} {d} h = coe (ap (λ z → z c d) (! (roundHom ℂ))) h

  isnat : {A B X : Set} {ℂ : Cat X} →
     ((c : X) → ([ ℂ , c ] → A) → ([ ℂ , c ] → B)) → Set
  isnat {A} {B} {X} {ℂ} z = (c d : X) (f : Hom ℂ c d) (k : [ ℂ , d ] → A)
    → z d k ∘ fct f == z c (k ∘ fct f)

  injf : {A B X : Set} {ℂ : Cat X} →
    (A → B) → Σ ((c : X) → ([ ℂ , c ] → A) → ([ ℂ , c ] → B)) isnat
  injf f = (λ c g → f ∘ g) , (λ c d f0 k → idp)

  postulate
    injf-equiv : {A B X : Set} {ℂ : Cat X} → is-equiv (injf {A} {B} {X} {ℂ})

-- I conjecture now that it's more canonical to demand the process of
-- realizing a type as a presheaf is invertible.

record PshOver {X : Set} (ℂ : Cat X) : Set₁ where
  open Cat ℂ
  field
    opart : X → Set
    fpart : {x y : X} → hom y x → opart x → opart y
    presId : {x : X} (e : opart x) → fpart id e == e
    pres⋆ : {x y z : X} (f : hom y x) (g : hom z y) (e : opart x)
      → fpart (g ⋆ f) e == fpart g (fpart f e)

interp : {X : Set} {ℂ : Cat X} → Set → PshOver ℂ
interp {X} {ℂ} S = record {
  opart = λ x → [ ℂ , x ] → S ;
  fpart =  λ f w → w ∘ funcOfMor f ;
-- Arg, actually proving these totally ought to be easy but so far I
-- seems to involve so much equality and PathOver shenanigans that I
-- get tired.
  presId = λ e → ap (e ∘_) (idlemma ℂ) ;
  pres⋆ = λ f g e → ap (e ∘_) {!!} }

-- The thing I really want to postulate:
postulate
  repna : {X : Set} {ℂ : Cat X} → is-equiv (interp {X} {ℂ})
