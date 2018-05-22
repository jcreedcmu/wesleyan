{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import 2018-05-22
open import 2018-05-22-rewrites

{- The point of this file is to specify the end-like equalizer
   constraints at a bunch of example types until I can see the
   pattern. -}

module 2018-05-22c (d e : Obj1) (f : Mor1 d e) where

open import 2018-05-22b d e f

module eD+--
       (a : oA (d , e))
       (b : oB- (d , e) (mA ff a))
       (c : oC-+ (d , e) (mA ff a) b) where
  X : Set
  X = oD+-- (e , d) (mA ff a) b c
  L R : X
  L = mD+-- fd α b c (tD+-- d α β (mC-+ df α b c)) where
    α : oA (d , d)
    α = mA df a
    β : oB- (d , d) α
    β = mB- df α b
  R = mD+-- ef α b c (tD+-- e α β (mC-+ fe α b c)) where
    α : oA (e , e)
    α = mA fe a
    β : oB- (e , e) α
    β = mB- fe α b
