{-# OPTIONS --without-K #-}
module Exercise3 where

open import HoTT hiding (_≤_ ; S)
open import Relational
import Exercise1

pullf : {B C : Set} → B ⊔ (B ⊔ C) → (B ⊔ C)
pullf = cpf inl idn

cpf-lem : {B C X : Set} (g : B → X) (h : C → X) → cpf g (cpf g h) == cpf g h ∘ (cpf inl idn)
cpf-lem {B} {C} g h = cpf-eq (cpf g h)

-- join of two relations over overlapping support
join : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h)) → fib (cpf g h)
join {g = g} {h} R S = pull pullf (transport fib (cpf-lem g h) (copair R S))

{- A preview of the theorem we prove at the bottom is:

jointriv : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → push inl (join R S) == R

The square we'll want to apply the beck-chevalley condition to is

                cart
     B ⊔ C → X --------> B ⊔ (B ⊔ C) → X
          | _|           |
   opcart |              | opcart
          |              |
          v              v
       B → X ---------> B ⊔ B → X
                cart

so the assignment to the arguments of the postulate is
f := cpf g h, plus the b1, k1, b2, k2 below:
-}

module _ {B C : Set} where
  b1 : B ⊔ (B ⊔ C) → (B ⊔ C)
  b1 = pullf
  k1 : B ⊔ B → B ⊔ (B ⊔ C)
  k1 = cpf inl (inr ∘ inl)
  b2 : B → B ⊔ C
  b2 = inl
  k2 : B ⊔ B → B
  k2 = cpf idn idn

  -- The b's and k's commute appropriately:
  b1k1~b2k2 : (x : B ⊔ B) → b1 (k1 x) == b2 (k2 x)
  b1k1~b2k2 (inl _) = idp
  b1k1~b2k2 (inr _) = idp

{- some abbreviations for commonly repeated bits -}
trf : {B C X : Set} (g : B → X) (h : C → X) → B ⊔ (B ⊔ C) → X
trf g h = cpf g h ∘ cpf inl idn

trblob : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h))
  → fib (trf g h)
trblob {g = g} {h} R S = transport fib (cpf-eq (cpf g h)) (copair R S)

trblob2 : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h))
  → fib (cpf g (cpf g h) ∘ k1)
trblob2 {g = g} {h} R S =
  (transport fib (cpf-eq (cpf g (cpf g h))) (copair (push idn R) (push inl S)))


t~ : {B C X : Set} (g : B → X) (h : C → X)
   → fib (cpf g h ∘ b1 ∘ k1)
   → fib (cpf g h ∘ b2 ∘ k2 {C = C})
t~ g h = transport (λ z → fib (cpf g h ∘ z)) (λ= b1k1~b2k2)

t~2 : {B C X : Set} (g : B → X) (h : C → X)
  → fib (cpf g (cpf g h) ∘ k1)
  → fib (trf g h ∘ k1)
t~2 g h = transport (λ z → fib (z ∘ k1)) (cpf-eq (cpf g h))

pushk1 : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h))
  → fib (trf g h ∘ k1)
pushk1 {g = g} {h} R S = push k1 (trblob R S)

pushk2 : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h))
  → fib (trf g h ∘ k1)
pushk2 {g = g} {h} R S = t~2 g h (push k1 (copair R S))

pushk3 : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h))
  → fib (trf g h ∘ k1)
pushk3 {g = g} {h} R S = t~2 g h (trblob2 R S)

pushk4 : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h))
  → fib (trf g h ∘ k1)
pushk4 {g = g} {h} R S =
  transport fib (ap (_∘ k1) (cpf-eq (cpf g h))) (trblob2 R S)

{- use push-transport here: -}
pushk1-lem :
  {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h)) →
  pushk1 R S == pushk2 R S
pushk1-lem g h R S = push-transport k1 (copair R S) (cpf-eq (cpf g h))

{- use copair-pres-push here: -}
pushk2-lem :
  {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h)) →
  pushk2 R S == pushk3 R S
pushk2-lem {B} {C} {X} g h R S =
   ap (t~2 g h) (copair-pres-push g (cpf g h) idn inl R S)

{- use transport-sub here: -}
pushk3-lem :
  {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h)) →
  pushk3 R S == pushk4 R S
pushk3-lem {B} {C} {X} g h R S =
    transport-sub fib (_∘ k1) (cpf-eq (cpf g h)) (trblob2 R S)

jointriv8 : {B C X : Set} (g : B → X) (h : C → X)  →
  (z : B ⊔ B) →
  app= (cpf-eq (cpf g (cpf g h)) ∙
    ap (_∘ k1) (cpf-eq (cpf g h)) ∙
    ap (cpf g h ∘_) (λ= b1k1~b2k2) ) z
      ==
  cpf-eq0 g z

jointriv8 {B} {C} g h (inl _)= {!!}
jointriv8 {B} {C} g h (inr _)= {!!}

{- 8. Mucking about with extensionality -}
jointriv7 : {B C X : Set} (g : B → X) (h : C → X)  →
  cpf-eq (cpf g (cpf g h)) ∙
    ap (_∘ k1) (cpf-eq (cpf g h)) ∙
    ap (cpf g h ∘_) (λ= b1k1~b2k2)
  == cpf-eq g
jointriv7 g h = λ=-η _ ∙ ap λ= (λ= (jointriv8 g h))

{- 7. Figure out the equality-of-paths we need: -}
jointriv6 : {B C X : Set} (g : B → X) (h : C → X)  →
  (q : fib (cpf g g)) →
  transport fib (cpf-eq g) q ==
  transport fib (ap (cpf g h ∘_) (λ= b1k1~b2k2))
    (transport fib (ap (_∘ k1) (cpf-eq (cpf g h)))
      (transport fib (cpf-eq (cpf g (cpf g h))) q))
jointriv6 g h q = transport-lem fib q
  (cpf-eq (cpf g (cpf g h)))
  (ap (_∘ k1) (cpf-eq (cpf g h)))
  (ap (cpf g h ∘_) (λ= b1k1~b2k2))
  (cpf-eq g)
  (jointriv7 g h)

{- 6. Call transport-sub one more time: -}
jointriv5 : {B C X : Set} (g : B → X) (h : C → X)  →
  (q : fib (cpf g g)) →
  transport fib (cpf-eq g) q ==
  transport (λ z → fib (cpf g h ∘ z)) (λ= b1k1~b2k2)
    (transport fib (ap (_∘ k1) (cpf-eq (cpf g h)))
      (transport fib (cpf-eq (cpf g (cpf g h))) q))
jointriv5 g h q = jointriv6 g h q ∙
  ! (transport-sub fib (cpf g h ∘_) (λ= b1k1~b2k2)
      (transport fib (ap (_∘ k1) (cpf-eq (cpf g h)))
        (transport fib (cpf-eq (cpf g (cpf g h))) q)))

{- 5. Do the last bit of 'interesting' work, matching up the copairs
      and invoking pushk{1,2,3}-lem: -}
jointriv4 : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h)) →
  transport fib (cpf-eq g) (copair R (push inl S)) == t~ g h (pushk1 R S)
jointriv4 g h R S =
  ap (λ z → transport fib (cpf-eq g) (copair z (push inl S))) (! (push-act0 R)) ∙
  jointriv5 g h (copair (push idn R) (push inl S)) ∙
  ! (ap (t~ g h)
        (pushk1-lem g h R S
        ∙ pushk2-lem g h R S
        ∙ pushk3-lem g h R S))

{- 4. We descend into the parts that matter,
      and use the fact that p : push inl S == triv g. -}
jointriv3 : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → Exercise1.join g R (triv g) ==
      pull (cpf idn idn)
      (transport (λ z → fib (cpf g h ∘ z)) (λ= b1k1~b2k2)
       (push k1 (trblob R S)))
jointriv3 g h R S p =
  ap (pull (cpf idn idn))
    (ap (λ z → transport fib (cpf-eq g) (copair R z)) (! p) ∙ jointriv4 g h R S)

{- 3. We take advantage of the work we already did in Exercise1 -}
jointriv2 : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → pull (k2 {C = C})
      (transport (λ z → fib (cpf g h ∘ z)) (λ= b1k1~b2k2)
       (push k1 (trblob R S)))
      == R
jointriv2 {B} {C} g h R S p = ! (Exercise1.jointriv g R ∙ jointriv3 g h R S p)

{- 2. We transform the goal with beck-chevalley, and expand
      cpf-lem g h -β-> cpf-eq (cpf g h). -}
jointriv1 : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → push inl (pull {f = cpf g h} pullf (trblob R S)) == R
jointriv1 {B} {C} g h R S p =
  beck-chevalley {k1 = k1} (λ= b1k1~b2k2) (trblob R S)
  ∙ jointriv2 g h R S p

{- 1. We expand the definition of join... -}
jointriv : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → push inl (join R S) == R
jointriv g h R S p = jointriv1 g h R S p

{- 0. This part of the story can be read backwards... -}
