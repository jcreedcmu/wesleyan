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

  mA/red1 : (c d : Obj1) (a : oA (c , d)) (f : Mor1 c d) →
    (mA (f , idm c) (mA (idm c , f) a)) ↦ mA (f , f) a
  {-# REWRITE mA/red1 #-}
  mA/red2 : (c d : Obj1) (a : oA (c , d)) (f : Mor1 c d) →
    (mA (idm d , f) (mA (f , idm d) a)) ↦ mA (f , f) a
  {-# REWRITE mA/red2 #-}

  oB+ : (δ : Obj) (a : oA δ) → Set
  mB+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) → oB+ δ a → oB+ ε (mA φ a)
  tB+ : (c : Obj1) (a : oA (c , c)) → oB+ (c , c) a

  mB+/red1 : (c d : Obj1) (a : oA (c , d)) (b : oB+ (c , d) a) (f : Mor1 c d) →
    (mB+ (f , idm c) (mA (idm c , f) a) (mB+ (idm c , f) a b))
    ↦ mB+ (f , f) a b
  {-# REWRITE mB+/red1 #-}
  mB+/red2 : (c d : Obj1) (a : oA (c , d)) (b : oB+ (c , d) a) (f : Mor1 c d) →
    (mB+ (idm d , f) (mA (f , idm d) a) (mB+ (f , idm d) a b))
    ↦ mB+ (f , f) a b
  {-# REWRITE mB+/red2 #-}

  oB- : (δ : Obj) (a : oA (~ δ)) → Set
  mB- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) → oB- δ (mA (~m φ) a) → oB- ε a
  tB- : (c : Obj1) (a : oA (c , c)) → oB- (c , c) a

  oC++ : (δ : Obj) (a : oA δ) (b : oB+ δ a) → Set
  mC++ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB+ δ a) → oC++ δ a b → oC++ ε (mA φ a) (mB+ φ a b)
  tC++ : (c : Obj1) → (a : oA (c , c)) (b : oB+ (c , c) a) → oC++ (c , c) a b

  oC-+ : (δ : Obj) (a : oA (~ δ)) (b : oB- δ a) → Set
  mC-+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB- δ (mA (~m φ) a)) → oC-+ δ (mA (~m φ) a) b → oC-+ ε a (mB- φ a b)
  tC-+ : (c : Obj1) → (a : oA (c , c)) (b : oB- (c , c) a) → oC-+ (c , c) a b

  oC+- : (δ : Obj) (a : oA δ) (b : oB- (~ δ) a) → Set
  mC+- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB- (~ ε) (mA φ a)) → oC+- δ a (mB- (~m φ) a b) → oC+- ε (mA φ a) b
  tC+- : (c : Obj1) → (a : oA (c , c)) (b : oB- (c , c) a) → oC+- (c , c) a b

  oC-- : (δ : Obj) (a : oA (~ δ)) (b : oB+ (~ δ) a) → Set
  mC-- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB+ (~ ε) a) → oC-- δ (mA (~m φ) a) (mB+ (~m φ) a b) → oC-- ε a b
  tC-- : (c : Obj1) → (a : oA (c , c)) (b : oB+ (c , c) a) → oC-- (c , c) a b

module common (c d : Obj1) (f : Mor1 c d) where
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

 module eC-+ (a : oA (c , d)) (b : oB- (d , c) a) where
   L = mC-+ {!!} {!!} {!!} {!!}
