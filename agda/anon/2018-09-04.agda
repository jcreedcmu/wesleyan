{-# OPTIONS --without-K #-}
open import HoTT

module 2018-09-04 where

record Conv {m n p q}
  {I : Set m} {J : Set n}
  (R : I → J → Set p)
  (A : I → Set q)
  (j : J) : Set (lmax q (lmax m p))
  where
  constructor conv
  field
    i : I
    a : A i
    r : R i j

_i×_ : ∀ {m1 m2 n1 n2} {I : Set m1} {J : Set m2} (A : I → Set n1) (B : J → Set n2) → (I × J) → Set (lmax n1 n2)
(A i× B)(i , j) = A i × B j

_⊗_ : ∀ {m} (A B : Set m → Set (lsucc m)) → Set m → Set (lsucc m)
_⊗_ A B = Conv (λ { (a , b) c → a × b == c }) (A i× B)

_p×_ : ∀ {m} (A B : Set m → Set (lsucc m)) → Set m → Set (lsucc m)
_p×_ A B = Conv (λ { (a , b) c → (a == c) × (b == c) }) (A i× B)


-- _⊗2_ : ∀ {m n} (A B : Set m → Set n) → Set m → Set n
-- _⊗2_ A B = Conv (λ { (a , b) c → a × b == c }) (A i× B)
