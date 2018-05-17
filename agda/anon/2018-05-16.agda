{-# OPTIONS --without-K --rewriting #-}
module 2018-05-16 where

-- open import HoTT

postulate
  Obj : Set
  Mor : Obj → Obj → Set
  oA : Obj → Set
  mA+ : {δ ε : Obj} → Mor δ ε → oA δ → oA ε
  mA- : {δ ε : Obj} → Mor δ ε → oA ε → oA δ

  oB : (δ : Obj) → oA δ → Set
  mB++ : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) → oB δ a → oB ε (mA+ φ a)
  mB-+ : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) → oB δ (mA- φ a) → oB ε a
  mB+- : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) → oB ε (mA+ φ a) → oB δ a
  mB-- : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) → oB ε a → oB δ (mA- φ a)

  oC : (δ : Obj) (a : oA δ) → oB δ a → Set
  mC+++ : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB δ a) → oC δ a b → oC ε (mA+ φ a) (mB++ φ a b)
  mC++- : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB δ a) → oC ε (mA+ φ a) (mB++ φ a b) → oC δ a b
  mC+-+ : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB ε (mA+ φ a)) → oC δ a (mB+- φ a b) → oC ε (mA+ φ a) b
  mC+-- : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB ε (mA+ φ a)) → oC ε (mA+ φ a) b → oC δ a (mB+- φ a b)
  mC-++ : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB δ (mA- φ a)) → oC δ (mA- φ a) b → oC ε a (mB-+ φ a b)
  mC-+- : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB δ (mA- φ a)) → oC ε a (mB-+ φ a b) → oC δ (mA- φ a) b
  mC--+ : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB ε a) → oC δ (mA- φ a) (mB-- φ a b) → oC ε a b
  mC--- : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB ε a) → oC ε a b → oC δ (mA- φ a) (mB-- φ a b)

  oD : (δ : Obj) (a : oA δ) (b : oB δ a) → oC δ a b → Set
  mD++++ : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB δ a) (c : oC δ a b) → oD δ a b c → oD ε (mA+ φ a) (mB++ φ a b) (mC+++ φ a b c)
  mD++-+ : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB δ a) (c : oC ε (mA+ φ a) (mB++ φ a b)) → oD δ a b (mC++- φ a b c) → oD ε (mA+ φ a) (mB++ φ a b) c
  mD+-++ : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB ε (mA+ φ a)) (c : oC δ a (mB+- φ a b)) → oD δ a (mB+- φ a b) c → oD ε (mA+ φ a) b (mC+-+ φ a b c)
  mD+--+ : {δ ε : Obj} (φ : Mor δ ε) (a : oA δ) (b : oB ε (mA+ φ a)) (c : oC ε (mA+ φ a) b) → oD δ a (mB+- φ a b) (mC+-- φ a b c) → oD ε (mA+ φ a) b c
  mD-+++ : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB δ (mA- φ a)) (c : oC δ (mA- φ a) b) → oD δ (mA- φ a) b c → oD ε a (mB-+ φ a b) (mC-++ φ a b c)
  mD-+-+ : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB δ (mA- φ a)) (c : oC ε a (mB-+ φ a b)) → oD δ (mA- φ a) b (mC-+- φ a b c) → oD ε a (mB-+ φ a b) c
  mD--++ : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB ε a) (c : oC δ (mA- φ a) (mB-- φ a b)) → oD δ (mA- φ a) (mB-- φ a b) c → oD ε a b (mC--+ φ a b c)
  mD---+ : {δ ε : Obj} (φ : Mor δ ε) (a : oA ε) (b : oB ε a) (c : oC ε a b) → oD δ (mA- φ a) (mB-- φ a b) (mC--- φ a b c) → oD ε a b c
