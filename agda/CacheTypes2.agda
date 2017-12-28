{-# OPTIONS --without-K #-}
module CacheTypes2 where

open import HoTT

record Cset : Set₁ where
  constructor cset
  field
    {C} : Set
    r e : C → C
    idemr : (c : C) → r (r c) == r c
    ideme : (c : C) → e (e c) == e c
    absorb1 : (c : C) → e (r c) == e c
    absorb2 : (c : C) → e (e c) == e c

valid : (S1 S2 : Cset) → (Cset.C S1 → Cset.C S2) → Set
valid (cset {C1} r1 e1 _ _ _ _)
      (cset {C2} r2 e2 _ _ _ _) f
      = (∀ c → (e2 ∘ f ∘ r1)(c) == (e2 ∘ f ∘ e1)(c))
        × (∀ c → (r2 ∘ f ∘ r1)(c) == (f ∘ r1)(c))

Cmor : (S1 S2 : Cset) → Set
Cmor S1 S2 = Σ (Cset.C S1 → Cset.C S2) (valid S1 S2)

postulate
  B D : Set
  z : B → D
  k : B → B
  decide : (b1 b2 : B) → (b1 == b2) ⊔ ⊤
  -- there exists some point b0 in B such that it's observably
  -- different (under observation z) after being hit with k.
  b0 : B
  b0diffz : ¬ (z b0 == z (k b0))

-- ... of course, this means in particular that k must move it.
b0moves : ¬ (b0 == k b0)
b0moves q = b0diffz (ap z q)

decCase : {b1 b2 : B} {A : Set} → (b1 == b2) ⊔ ⊤ → (b1 == b2 → A) → A → A
decCase (inl x) f g = f x
decCase (inr x) f g = g

pattern some x = inl x
pattern none = inr tt

C : Set
C = B × (D ⊔ ⊤)

r : B × (D ⊔ ⊤) → B × (D ⊔ ⊤)
r (b , some _) = b , (some (z b))
r (b , none) = b , none

e : C → C
e (b , _) = b , none

idemr : (c : C) → r (r c) == r c
idemr (b , some _) = idp
idemr (b , none) = idp

ideme : (c : C) → e (e c) == e c
ideme (b , some _) = idp
ideme (b , none) = idp

absorb1 : (c : C) → e (r c) == e c
absorb1 (b , some _) = idp
absorb1 (b , none) = idp

absorb2 : (c : C) → e (e c) == e c
absorb2 (b , some _) = idp
absorb2 (b , none) = idp

Simple : Cset
Simple = record {
  C = C ; r = r ; e = e ;
  idemr = idemr ; ideme = ideme ;
  absorb1 = absorb1 ; absorb2 = absorb2 }

f1 : C → C
f1 (b , χ) = k b , none

f2 : C → C
f2 (b , χ) = k b , decCase (decide b (k b)) (λ _ → χ) none

f3 : C → C
f3 (b , χ) = b , some (z b)

valid1 : valid Simple Simple f1
valid1 = lem , (λ _ → idp) where
  lem : (c : C) → (e ∘ f1 ∘ r) c == (e ∘ f1 ∘ e) c
  lem (b , some _) = idp
  lem (b , none) = idp

valid2 : valid Simple Simple f2
valid2 = lem , lem2 where
  lem : (c : C) → (e ∘ f2 ∘ r) c == (e ∘ f2 ∘ e) c
  lem (b , some _) = idp
  lem (b , none) = idp
  lem2 : (c : C) → (r ∘ f2 ∘ r) c == (f2 ∘ r) c
  lem2 (b , some x) with decide b (k b)
  lem2 (b , some x) | some y = ap (λ x → k b , inl (z x)) (! y)
  lem2 (b , some x) | none = idp
  lem2 (b , none) with decide b (k b)
  lem2 (b , none) | some y = idp
  lem2 (b , none) | none = idp

valid3 : valid Simple Simple f3
valid3 = lem , (λ _ → idp) where
  lem : (c : C) → (e ∘ f3 ∘ r) c == (e ∘ f3 ∘ e) c
  lem (b , some _) = idp
  lem (b , none) = idp

f4 : C → C
f4 (b , none) = (k b , none)
f4 (b , some _) = (b , none)

f5 : C → C
f5 (b , χ) = k b , χ

inlEq : {A B : Set} {x y : A} → _==_ {A = A ⊔ B} (inl x) (inl y) → x == y
inlEq {x = x} {.x} idp = idp

notValid4 : ¬ (valid Simple Simple f4)
notValid4 (v1 , v2) = b0moves (ap fst lem) where
  lem : b0 , inr unit == k b0 , inr unit
  lem = v1 (b0 , some (z b0))

notValid5 : ¬ (valid Simple Simple f5)
notValid5 (v1 , v2) = b0diffz (! (inlEq (ap snd lem))) where
  lem : k b0 , inl (z (k b0)) == k b0 , inl (z b0)
  lem = v2 (b0 , some (z b0))
