{-# OPTIONS --without-K #-}
module Exercise1 where

open import HoTT hiding (_≤_ ; S)
open import Relational

-- product of two relations over the same support
join : {B X : Set} (f : B → X) (R S : fib f) → fib f
join f R S = pull (cpf idn idn) (transport fib (cpf-eq f) (copair R S))

-- joining with a trivial relation is the identity
jointriv : {B X : Set} (f : B → X) (R : fib f) → R == join f R (triv f)
jointriv f R = ≤anti R (join f R (triv f)) jointriv1 jointriv2 where
  jointriv1 : R ≤ join f R (triv f)
  jointriv1 = –> (copair= f R (triv f) R) (≤=r (! (pull-act0 R)) , ≤t (zero=s R) (≤=r (!(pull-act0 (triv f)))))

  jointriv2a : join f R (triv f) ≤ pull idn R
  jointriv2a = <– (copair= f R (triv f) (join f R (triv f))) (≤r (join f R (triv f))) .fst

  jointriv2 : join f R (triv f) ≤ R
  jointriv2 = ≤t jointriv2a (≤=r (pull-act0 R))
