{-# OPTIONS --without-K --rewriting #-}
module 2018-05-22 where

open import HoTT

postulate
  Obj1 : Set
  Mor1 : Obj1 → Obj1 → Set
  idm : (c : Obj1) → Mor1 c c

Obj : Set
Obj = Obj1 × Obj1

Mor : Obj → Obj → Set
Mor (d , d') (e , e') = Mor1 d e × Mor1 e' d'

~ : Obj → Obj
~ (d , d') = (d' , d)

~m : {δ ε : Obj} → Mor δ ε → Mor (~ ε) (~ δ)
~m (f , f') = (f' , f)

postulate
  oA : (δ : Obj) → Set
  mA : {δ ε : Obj} (φ : Mor δ ε) → oA δ → oA ε

  mA-red1 : (c d : Obj1) (a : oA (c , d)) (f : Mor1 c d) →
    (mA (f , idm c) (mA (idm c , f) a)) ↦ mA (f , f) a
  {-# REWRITE mA-red1 #-}
  mA-red2 : (c d : Obj1) (a : oA (c , d)) (f : Mor1 c d) →
    (mA (idm d , f) (mA (f , idm d) a)) ↦ mA (f , f) a
  {-# REWRITE mA-red2 #-}

  oB+ : (δ : Obj) (a : oA δ) → Set
  mB+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) → oB+ δ a → oB+ ε (mA φ a)
  tB+ : (c : Obj1) (a : oA (c , c)) → oB+ (c , c) a
  eB+ : (c d : Obj1) (a : oA (c , d)) (f : Mor1 c d)
    → mB+ (f , idm c) (mA (idm c , f) a) (tB+ c (mA (idm c , f) a)) ==
      mB+ (idm d , f) (mA (f , idm d) a) (tB+ d (mA (f , idm d) a))

  oB- : (δ : Obj) (a : oA (~ δ)) → Set
  mB- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) → oB- δ (mA (~m φ) a) → oB- ε a
  tB- : (c : Obj1) (a : oA (c , c)) → oB- (c , c) a
  eB- : (c d : Obj1) (a : oA (c , d)) (f : Mor1 c d)
    → mB- (f , idm c) a (tB- c (mA (idm c , f) a)) ==
      mB- (idm d , f) a (tB- d (mA (f , idm d) a))

  oC++ : (δ : Obj) (a : oA δ) (b : oB+ δ a) → Set
  mC++ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB+ δ a) → oC++ δ a b → oC++ ε (mA φ a) (mB+ φ a b)

  oC-+ : (δ : Obj) (a : oA (~ δ)) (b : oB- δ a) → Set
  mC-+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB- δ (mA (~m φ) a)) → oC-+ δ (mA (~m φ) a) b → oC-+ ε a (mB- φ a b)

  oC+- : (δ : Obj) (a : oA δ) (b : oB- (~ δ) a) → Set
  mC+- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB- (~ ε) (mA φ a)) → oC+- δ a (mB- (~m φ) a b) → oC+- ε (mA φ a) b

  oC-- : (δ : Obj) (a : oA (~ δ)) (b : oB+ (~ δ) a) → Set
  mC-- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB+ (~ ε) a) → oC-- δ (mA (~m φ) a) (mB+ (~m φ) a b) → oC-- ε a b
