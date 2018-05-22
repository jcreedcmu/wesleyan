{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import 2018-05-22
open import 2018-05-22-rewrites

{- The point of this file is to specify some more end-like equalizer
   constraints at a bunch of example types until I can see the
   pattern. -}

module 2018-05-22c (d e : Obj1) (f : Mor1 d e) where

dd de ed ee : Obj
dd = (d , d)
de = (d , e)
ed = (e , d)
ee = (e , e)

df : Mor de dd
df = (idm d , f)

fe : Mor de ee
fe = (f , idm e)

ef : Mor ee ed
ef = (idm e , f)

fd : Mor dd ed
fd = (f , idm d)

ff : Mor de ed
ff = (f , f)

module eD-+-
       (a : oA de)
       (b : oB- de (mA ff a))
       (c : oC+- de a (mB- ff a b)) where
  X : Set
  X = oD-+- ed a (mB- ff a b) c

  L R : X
  L = mD-+- fd a β c (tD-+- d α β γ) where
    α : oA dd
    α = mA df a
    β : oB- dd α
    β = mB- df α b
    γ : oC+- dd α β
    γ = mC+- df a β c
  R = mD-+- ef a β c (tD-+- e α β γ) where
    α : oA ee
    α = mA fe a
    β : oB- ee α
    β = mB- fe α b
    γ : oC+- ee α β
    γ = mC+- fe a β c

module eD--+
       (a : oA de)
       (b : oB+ de a)
       (c : oC-- de (mA ff a) (mB+ ff a b)) where
  X : Set
  X = oD--+ ed a b (mC-- ff a b c)

  L R : X
  L = mD--+ fd a b γ (tD--+ d α β γ) where
    α : oA dd
    α = mA df a
    β : oB+ dd α
    β = mB+ df a b
    γ : oC-- dd α β
    γ = mC-- df α β c
  R = mD--+ ef a b γ (tD--+ e α β γ) where
    α : oA ee
    α = mA fe a
    β : oB+ ee α
    β = mB+ fe a b
    γ : oC-- ee α β
    γ = mC-- fe α β c

module eD---
       (a : oA de)
       (b : oB+ de a)
       (c : oC++ de a b) where
  X : Set
  X = oD--- ed a b c

  L R : X
  L = mD--- fd a b c (tD--- d α β γ) where
    α : oA dd
    α = mA df a
    β : oB+ dd α
    β = mB+ df a b
    γ : oC++ dd α β
    γ = mC++ df a b c
  R = mD--- ef a b c (tD--- e α β γ) where
    α : oA ee
    α = mA fe a
    β : oB+ ee α
    β = mB+ fe a b
    γ : oC++ ee α β
    γ = mC++ fe a b c
