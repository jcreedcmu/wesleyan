{-# OPTIONS --without-K --rewriting #-}
module 2018-06-15 where

open import HoTT

postulate
  *_ : Set → Set
  ι : {C : Set} → C → * * C
  σ : {a b : Set} → (* a) × (* b) → * (a × b)
  *f : {a b : Set} → (a → b) → (* a) → (* b)


_×f_ : {a b c d : Set} → (a → b) → (c → d) → (a × c) → (b × d)
(f ×f g) (x , y) = (f x , g y)

postulate
  ιnat : {C D : Set} → (f : C → D) (c : C)
    → *f (*f f) (ι c) == ι (f c)
  σnat : {A1 A2 B1 B2 : Set}  (f : A1 → A2) (g : B1 → B2)
    (a : * A1) (b : * B1)
    → *f (f ×f g) (σ (a , b)) == σ (*f f a , *f g b)

□ : Set → Set
□ C = (* C) × C

ε : {C : Set} → □ C → □ (□ C)
ε (x , y) = σ (ι y , x)  , (x , y)

δ : {C : Set} → □ C → C
δ (x , y) = y

assoc : {C : Set} (z : □ C) → ε (ε z) == ((*f ε) ×f ε) (ε z)
assoc (x , y) = pair×= (! foo) idp where
  foo :
    *f (λ xy → σ (ι (snd xy) , fst xy) , xy) (σ (ι y , x))
    == σ (ι (x , y) , σ (ι y , x))
  foo = {! !}
