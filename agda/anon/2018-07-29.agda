{-# OPTIONS --without-K --rewriting #-}
module 2018-07-29 where

open import HoTT

postulate
  Cat : Set

data Var : Set where
  cov cont : Var

Ftype = List (Cat × Var)

postulate
  Fun : Ftype → Set
  Elm : {τ : Ftype} → Fun τ → Set
  End Coend : {C : Cat} {τ : Ftype} → Fun ((C , cont) :: (C , cov) :: τ) → Fun τ
