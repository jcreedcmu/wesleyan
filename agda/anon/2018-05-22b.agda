{-# OPTIONS --without-K --rewriting #-}
module 2018-05-22b where

open import HoTT
open import 2018-05-22

postulate
  c d : Obj1
  f : Mor1 c d

cf : Mor (c , d) (c , c)
cf = (idm c , f)

fd : Mor (c , d) (d , d)
fd = (f , idm d)

df : Mor (d , d) (d , c)
df = (idm d , f)

fc : Mor (c , c) (d , c)
fc = (f , idm c)

-- for all of these, I can imagine postulating L == R, but I don't
-- actually need to use it anywhere, so don't actually do it.

module eB+ (a : oA (c , d)) where
  X : Set
  X = oB+ (d , c) (mA (f , f) a)
  L R : X
  L = mB+ fc (mA cf a) (tB+ c (mA cf a))
  R = mB+ df (mA fd a) (tB+ d (mA fd a))

module eB- (a : oA (c , d)) where
  X : Set
  X = oB- (d , c) a
  L R : X
  L = mB- fc a (tB- c (mA cf a))
  R = mB- df a (tB- d (mA fd a))

module eC++ (a : oA (c , d)) (b : oB+ (c , d) a) where
  X : Set
  X = oC++ (d , c) (mA (f , f) a) (mB+ (f , f) a b)
  L R : X
  L = mC++ fc (mA cf a) (mB+ cf a b) (tC++ c (mA cf a) (mB+ cf a b))
  R = mC++ df (mA fd a) (mB+ fd a b) (tC++ d (mA fd a) (mB+ fd a b))

module eC-+ (a : oA (c , d)) (b : oB- (c , d) (mA (f , f) a)) where
  X : Set
  X = oC-+ (d , c) a (mB- (f , f) a b)
  L R : X
  L = mC-+ fc a (mB- cf (mA cf a) b) (tC-+ c (mA cf a) (mB- cf (mA cf a) b))
  R = mC-+ df a (mB- fd (mA fd a) b) (tC-+ d (mA fd a) (mB- fd (mA fd a) b))

module eC+- (a : oA (c , d)) (b : oB- (c , d) (mA (f , f) a)) where
