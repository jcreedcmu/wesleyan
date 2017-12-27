{-# OPTIONS --without-K #-}
module CacheTypes where

open import HoTT

record Section (A B : Set) : Set where
  constructor sec
  field
    epi : A → B
    mono : B → A
    eqn : (b : B) → epi (mono b) == b

record Cset : Set₁ where
  constructor cset
  field
    {C G B} : Set
    pg : Section C G
    πι : Section G B

valid : (S1 S2 : Cset) → (Cset.C S1 → Cset.C S2) → Set
valid (cset {C1} {G1} {B1} (sec p1 g1 pg1) (sec π1 ι1 πι1))
      (cset {C2} {G2} {B2} (sec p2 g2 pg2) (sec π2 ι2 πι2)) f
      = (∀ x → (g2 ∘ p2 ∘ f ∘ g1)(x) == (f ∘ g1)(x))
        × (∀ x → (π2 ∘ p2 ∘ f ∘ g1)(x) == (π2 ∘ p2 ∘ f ∘ g1 ∘ ι1 ∘ π1)(x))

Cmor : (S1 S2 : Cset) → Set
Cmor S1 S2 = Σ (Cset.C S1 → Cset.C S2) (valid S1 S2)

postulate
  B D : Set
  z : B → D
  k : B → B
  decide : (b1 b2 : B) → (b1 == b2) ⊔ ⊤

decCase : {b1 b2 : B} {A : Set} → (b1 == b2) ⊔ ⊤ → (b1 == b2 → A) → A → A
decCase (inl x) f g = f x
decCase (inr x) f g = g

some : {D : Set} → D → D ⊔ ⊤
some = inl

none : {D : Set} → D ⊔ ⊤
none = inr tt

C : Set
C = B × (D ⊔ ⊤)

G : Set
G = B × Bool

p : B × D ⊔ ⊤ → B × Bool
p (b , inl d) = b , true
p (b , none) = b , false

g : B × Bool → B × D ⊔ ⊤
g (b , true) = b , some (z b)
g (b , false) = b , none

π : B × Bool → B
π (b , _)= b

ι : B → B × Bool
ι b = (b , false)

pg : (b : B × Bool) → p (g b) == b
pg (b , true) = idp
pg (b , false) = idp

πι : (b : B) → π (ι b) == b
πι (b) = idp

Simple : Cset
Simple = record {
  C = C ;
  G = G ;
  B = B ;
  pg = sec p g pg ;
  πι = sec π ι πι }

f1 : C → C
f1 (b , χ) = k b , none

f2 : C → C
f2 (b , χ) = k b , decCase (decide b (k b)) (λ _ → χ) none

f3 : C → C
f3 (b , χ) = b , some (z b)

valid1 : valid Simple Simple f1
valid1 = (λ x → idp) , (λ x → ap k (lem x)) where
  lem : (x : B × Bool) → fst (Section.mono (Cset.pg Simple) x) == fst x
  lem (b , true) = idp
  lem (b , false) = idp

valid2 : valid Simple Simple f2
valid2 = lem2 , lem2b where
  lem2 : (x : B × Bool) →
     g (p (k (fst (g x)) ,
       decCase (decide (fst (g x)) (k (fst (g x)))) (λ _ → snd (g x))
       (inr unit)))
     ==
     k (fst (g x)) ,
     decCase (decide (fst (g x)) (k (fst (g x)))) (λ _ → snd (g x)) (inr unit)
  lem2 (b , true) with decide b (k b)
  lem2 (b , true) | inl w = pair×= idp (ap (inl ∘ z) (! w))
  lem2 (b , true) | inr _ = idp
  lem2 (b , false) with decide b (k b)
  lem2 (b , false) | inl w = idp
  lem2 (b , false) | inr _ = idp

  lem2b : (x : B × Bool) → fst
     (p
      (k (fst (g x)) ,
       decCase (decide (fst (g x)) (k (fst (g x)))) (λ _ → snd (g x))
       (inr unit)))
     ==
     fst
     (p
      (k (fst x) ,
       decCase (decide (fst x) (k (fst x))) (λ _ → inr unit) (inr unit)))
  lem2b (b , inl x) with decide b (k b)
  lem2b (b , inl x) | inl w = idp
  lem2b (b , inl x) | inr _ = idp
  lem2b (b , inr x) = idp

valid3 : valid Simple Simple f3
valid3 = (λ x → idp) , (λ x → lem3 x) where
  lem3 : (x : B × Bool) → fst (g x) == fst x
  lem3 (b , true) = idp
  lem3 (b , false) = idp
