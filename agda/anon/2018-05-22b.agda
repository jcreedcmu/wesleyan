{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import 2018-05-22
open import 2018-05-22-rewrites

{- The point of this file is to specify the end-like equalizer
   constraints at a bunch of example types until I can see the
   pattern. -}

module 2018-05-22b (d e : Obj1) (f : Mor1 d e) where

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

-- for all of these, I can imagine postulating L == R, but I don't
-- actually need to use it anywhere, so don't actually do it.

module eB+ (a : oA de) where
  X : Set
  X = oB+ ed (mA ff a)
  L R : X
  L = mB+ fd (mA df a) (tB+ d (mA df a))
  R = mB+ ef (mA fe a) (tB+ e (mA fe a))

module eB- (a : oA de) where
  X : Set
  X = oB- ed a
  L R : X
  L = mB- fd a (tB- d (mA df a))
  R = mB- ef a (tB- e (mA fe a))

module eC++ (a : oA de) (b : oB+ de a) where
  X : Set
  X = oC++ ed (mA ff a) (mB+ ff a b)
  L R : X
  L = mC++ fd (mA df a) (mB+ df a b) (tC++ d (mA df a) (mB+ df a b))
  R = mC++ ef (mA fe a) (mB+ fe a b) (tC++ e (mA fe a) (mB+ fe a b))

module eC-+ (a : oA de) (b : oB- de (mA ff a)) where
  X : Set
  X = oC-+ ed a (mB- ff a b)
  L R : X
  L = mC-+ fd a (mB- df (mA df a) b) (tC-+ d (mA df a) (mB- df (mA df a) b))
  R = mC-+ ef a (mB- fe (mA fe a) b) (tC-+ e (mA fe a) (mB- fe (mA fe a) b))

module eC+- (a : oA de) (b : oB- de (mA ff a)) where
  X : Set
  X = oC+- ed (mA ff a) b
  L R : X
  L = mC+- fd (mA df a) b (tC+- d (mA df a) (mB- df (mA df a) b))
  R = mC+- ef (mA fe a) b (tC+- e (mA fe a) (mB- fe (mA fe a) b))

module eC-- (a : oA de) (b : oB+ de a) where
  X : Set
  X = oC-- ed a b
  L R : X
  L = mC-- fd a b (tC-- d (mA df a) (mB+ df a b))
  R = mC-- ef a b (tC-- e (mA fe a) (mB+ fe a b))

module eD+++ (a : oA de) (b : oB+ de a) (c : oC++ de a b) where
  X : Set
  X = oD+++ ed (mA ff a) (mB+ ff a b) (mC++ ff a b c)
  L R : X
  L = mD+++ fd (mA df a) (mB+ df a b) (mC++ df a b c)
      (tD+++ d (mA df a) (mB+ df a b) (mC++ df a b c))
  R = mD+++ ef (mA fe a) (mB+ fe a b) (mC++ fe a b c)
      (tD+++ e (mA fe a) (mB+ fe a b) (mC++ fe a b c))

module eD++-
       (a : oA de)
       (b : oB+ de a)
       (c : oC-- de (mA ff a) (mB+ ff a b)) where
  X : Set
  X = oD++- ed (mA ff a) (mB+ ff a b) c
  L R : X
  L = mD++- fd α β c (tD++- d α β (mC-- df α β c)) where
    α : oA dd
    α = mA df a
    β : oB+ dd α
    β = mB+ df a b

  R = mD++- ef α β c (tD++- e α β (mC-- fe α β c)) where
    α : oA ee
    α = mA fe a
    β : oB+ ee α
    β = mB+ fe a b

module eD+-+
       (a : oA de)
       (b : oB- de (mA ff a))
       (c : oC+- de a (mB- ff a b)) where
  X : Set
  X = oD+-+ ed (mA ff a) b (mC+- ff a b c)
  L R : X
  L = mD+-+ fd α b γ (tD+-+ d α β γ) where
    α : oA dd
    α = mA df a
    β : oB- dd α
    β = mB- df α b
    γ : oC+- dd (mA df a) β
    γ = mC+- df a β c

  R = mD+-+ ef α b γ (tD+-+ e α β γ) where
    α : oA ee
    α = mA fe a
    β : oB- ee α
    β = mB- fe α b
    γ : oC+- ee (mA fe a) β
    γ = mC+- fe a β c

module eD+--
       (a : oA de)
       (b : oB- de (mA ff a))
       (c : oC-+ de (mA ff a) b) where
  X : Set
  X = oD+-- ed (mA ff a) b c
  L R : X
  L = mD+-- fd α b c (tD+-- d α β (mC-+ df α b c)) where
    α : oA dd
    α = mA df a
    β : oB- dd α
    β = mB- df α b
  R = mD+-- ef α b c (tD+-- e α β (mC-+ fe α b c)) where
    α : oA ee
    α = mA fe a
    β : oB- ee α
    β = mB- fe α b
