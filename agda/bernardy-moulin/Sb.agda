{-# OPTIONS --without-K --rewriting #-}
module Sb where

open import HoTT hiding ( O; Path; _*_ )

open import Sharp1

rel : {A : Set} {x : A} (y z : x ∈ i · A) → Set
rel {A} y z  = z ∈ i · ((y * i) ∈ j · A)

thm : {A : Set} {x : A} (y z : x ∈ i · A) →
  rel y z → rel z y
thm y z R = lam λ i → lam λ j → (R * j) * i
