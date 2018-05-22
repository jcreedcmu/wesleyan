{-# OPTIONS --without-K --rewriting #-}
module 2018-05-22b where

{- The point of this file is to specify the end-like equalizer
   constraints at a bunch of example types until I can see the
   pattern. -}

open import HoTT
open import 2018-05-22
open import 2018-05-22-rewrites

postulate
  d e : Obj1
  f : Mor1 d e

df : Mor (d , e) (d , d)
df = (idm d , f)

fe : Mor (d , e) (e , e)
fe = (f , idm e)

ef : Mor (e , e) (e , d)
ef = (idm e , f)

fd : Mor (d , d) (e , d)
fd = (f , idm d)

ff : Mor (d , e) (e , d)
ff = (f , f)

-- for all of these, I can imagine postulating L == R, but I don't
-- actually need to use it anywhere, so don't actually do it.

module eB+ (a : oA (d , e)) where
  X : Set
  X = oB+ (e , d) (mA ff a)
  L R : X
  L = mB+ fd (mA df a) (tB+ d (mA df a))
  R = mB+ ef (mA fe a) (tB+ e (mA fe a))

module eB- (a : oA (d , e)) where
  X : Set
  X = oB- (e , d) a
  L R : X
  L = mB- fd a (tB- d (mA df a))
  R = mB- ef a (tB- e (mA fe a))

module eC++ (a : oA (d , e)) (b : oB+ (d , e) a) where
  X : Set
  X = oC++ (e , d) (mA ff a) (mB+ ff a b)
  L R : X
  L = mC++ fd (mA df a) (mB+ df a b) (tC++ d (mA df a) (mB+ df a b))
  R = mC++ ef (mA fe a) (mB+ fe a b) (tC++ e (mA fe a) (mB+ fe a b))

module eC-+ (a : oA (d , e)) (b : oB- (d , e) (mA ff a)) where
  X : Set
  X = oC-+ (e , d) a (mB- ff a b)
  L R : X
  L = mC-+ fd a (mB- df (mA df a) b) (tC-+ d (mA df a) (mB- df (mA df a) b))
  R = mC-+ ef a (mB- fe (mA fe a) b) (tC-+ e (mA fe a) (mB- fe (mA fe a) b))

module eC+- (a : oA (d , e)) (b : oB- (d , e) (mA ff a)) where
  X : Set
  X = oC+- (e , d) (mA ff a) b
  L R : X
  L = mC+- fd (mA df a) b (tC+- d (mA df a) (mB- df (mA df a) b))
  R = mC+- ef (mA fe a) b (tC+- e (mA fe a) (mB- fe (mA fe a) b))

module eC-- (a : oA (d , e)) (b : oB+ (d , e) a) where
  X : Set
  X = oC-- (e , d) a b
  L R : X
  L = mC-- fd a b (tC-- d (mA df a) (mB+ df a b))
  R = mC-- ef a b (tC-- e (mA fe a) (mB+ fe a b))

module eD+++ (a : oA (d , e)) (b : oB+ (d , e) a) (c : oC++ (d , e) a b) where
  X : Set
  X = oD+++ (e , d) (mA ff a) (mB+ ff a b) (mC++ ff a b c)
  L R : X
  L = mD+++ fd (mA df a) (mB+ df a b) (mC++ df a b c)
      (tD+++ d (mA df a) (mB+ df a b) (mC++ df a b c))
  R = mD+++ ef (mA fe a) (mB+ fe a b) (mC++ fe a b c)
      (tD+++ e (mA fe a) (mB+ fe a b) (mC++ fe a b c))

module eD++-
       (a : oA (d , e))
       (b : oB+ (d , e) a)
       (c : oC-- (d , e) (mA ff a) (mB+ ff a b)) where
  X : Set
  X = oD++- (e , d) (mA ff a) (mB+ ff a b) c
  L R : X
  L = mD++- fd α β c (tD++- d α β (mC-- df α β c)) where
    α : oA (d , d)
    α = mA df a
    β : oB+ (d , d) α
    β = mB+ df a b

  R = mD++- ef α β c (tD++- e α β (mC-- fe α β c)) where
    α : oA (e , e)
    α = mA fe a
    β : oB+ (e , e) α
    β = mB+ fe a b

module eD+-+
       (a : oA (d , e))
       (b : oB+ (d , e) a)
       (c : oC-- (d , e) (mA ff a) (mB+ ff a b)) where
