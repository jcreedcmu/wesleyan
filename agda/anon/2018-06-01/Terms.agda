{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import 2018-06-01.Basics
open import 2018-06-01.Rewrites

module 2018-06-01.Terms {d e : Obj1} (f : Mor1 d e) where

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

module eA (t : tA) where
  X : Set
  X = oA ed
  L R : X
  L = mA fd (t d)
  R = mA ef (t e)

module eB+ (a : oA de) (t : tB+) where
  X : Set
  X = oB+ ed (mA ff a)
  L R : X
  L = mB+ fd (mA df a) (t d (mA df a))
  R = mB+ ef (mA fe a) (t e (mA fe a))

module eB- (a : oA de) (t : tB-) where
  X : Set
  X = oB- ed a
  L R : X
  L = mB- fd a (t d (mA df a))
  R = mB- ef a (t e (mA fe a))

module eC++ (a : oA de) (b : oB+ de a) (t : tC++) where
  X : Set
  X = oC++ ed (mA ff a) (mB+ ff a b)
  L R : X
  L = mC++ fd (mA df a) (mB+ df a b) (t d (mA df a) (mB+ df a b))
  R = mC++ ef (mA fe a) (mB+ fe a b) (t e (mA fe a) (mB+ fe a b))

module eC-+ (a : oA de) (b : oB- de (mA ff a)) (t : tC-+) where
  X : Set
  X = oC-+ ed a (mB- ff a b)
  L R : X
  L = mC-+ fd a (mB- df (mA df a) b) (t d (mA df a) (mB- df (mA df a) b))
  R = mC-+ ef a (mB- fe (mA fe a) b) (t e (mA fe a) (mB- fe (mA fe a) b))

module eC+- (a : oA de) (b : oB- de (mA ff a)) (t : tC+-) where
  X : Set
  X = oC+- ed (mA ff a) b
  L R : X
  L = mC+- fd (mA df a) b (t d (mA df a) (mB- df (mA df a) b))
  R = mC+- ef (mA fe a) b (t e (mA fe a) (mB- fe (mA fe a) b))

module eC-- (a : oA de) (b : oB+ de a) (t : tC--) where
  X : Set
  X = oC-- ed a b
  L R : X
  L = mC-- fd a b (t d (mA df a) (mB+ df a b))
  R = mC-- ef a b (t e (mA fe a) (mB+ fe a b))

module eD+++ (a : oA de) (b : oB+ de a) (c : oC++ de a b) (t : tD+++) where
  X : Set
  X = oD+++ ed (mA ff a) (mB+ ff a b) (mC++ ff a b c)
  L R : X
  L = mD+++ fd (mA df a) (mB+ df a b) (mC++ df a b c)
      (t d (mA df a) (mB+ df a b) (mC++ df a b c))
  R = mD+++ ef (mA fe a) (mB+ fe a b) (mC++ fe a b c)
      (t e (mA fe a) (mB+ fe a b) (mC++ fe a b c))

module eD++-
       (a : oA de)
       (b : oB+ de a)
       (c : oC-- de (mA ff a) (mB+ ff a b)) (t : tD++-) where
  X : Set
  X = oD++- ed (mA ff a) (mB+ ff a b) c
  L R : X
  L = mD++- fd α β c (t d α β (mC-- df α β c)) where
    α : oA dd
    α = mA df a
    β : oB+ dd α
    β = mB+ df a b

  R = mD++- ef α β c (t e α β (mC-- fe α β c)) where
    α : oA ee
    α = mA fe a
    β : oB+ ee α
    β = mB+ fe a b

module eD+-+
       (a : oA de)
       (b : oB- de (mA ff a))
       (c : oC+- de a (mB- ff a b)) (t : tD+-+) where
  X : Set
  X = oD+-+ ed (mA ff a) b (mC+- ff a b c)
  L R : X
  L = mD+-+ fd α b γ (t d α β γ) where
    α : oA dd
    α = mA df a
    β : oB- dd α
    β = mB- df α b
    γ : oC+- dd (mA df a) β
    γ = mC+- df a β c

  R = mD+-+ ef α b γ (t e α β γ) where
    α : oA ee
    α = mA fe a
    β : oB- ee α
    β = mB- fe α b
    γ : oC+- ee (mA fe a) β
    γ = mC+- fe a β c

module eD+--
       (a : oA de)
       (b : oB- de (mA ff a))
       (c : oC-+ de (mA ff a) b) (t : tD+--) where
  X : Set
  X = oD+-- ed (mA ff a) b c
  L R : X
  L = mD+-- fd α b c (t d α β (mC-+ df α b c)) where
    α : oA dd
    α = mA df a
    β : oB- dd α
    β = mB- df α b
  R = mD+-- ef α b c (t e α β (mC-+ fe α b c)) where
    α : oA ee
    α = mA fe a
    β : oB- ee α
    β = mB- fe α b

module eD-++
       (a : oA de)
       (b : oB- de (mA ff a))
       (c : oC-+ de (mA ff a) b) (t : tD-++) where
  X : Set
  X = oD-++ ed a (mB- ff a b) (mC-+ ff a b c)

  L R : X
  L = mD-++ fd a β γ (t d α β γ) where
    α : oA dd
    α = mA df a
    β : oB- dd α
    β = mB- df α b
    γ : oC-+ dd α (mB- df α b)
    γ = mC-+ df α b c

  R = mD-++ ef a β γ (t e α β γ) where
    α : oA ee
    α = mA fe a
    β : oB- ee α
    β = mB- fe α b
    γ : oC-+ ee α (mB- fe α b)
    γ = mC-+ fe α b c
