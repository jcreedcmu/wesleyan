{-# OPTIONS --without-K --rewriting #-}
module 2018-06-01.Basics where

open import HoTT

{- The category ⟪Δ⟫ -}
postulate
  Obj1 : Set
  Mor1 : Obj1 → Obj1 → Set
  idm : (c : Obj1) → Mor1 c c

{- The category ⟦Δ⟧ -}
Obj : Set
Obj = Obj1 × Obj1

Mor : Obj → Obj → Set
Mor (d , d') (e , e') = Mor1 d e × Mor1 e' d'

~ : Obj → Obj
~ (d , d') = (d' , d)

~m : {δ ε : Obj} → Mor δ ε → Mor (~ ε) (~ δ)
~m (f , f') = (f' , f)

postulate
  -- Δ ⊢ A : type
  oA : (δ : Obj) → Set
  mA : {δ ε : Obj} (φ : Mor δ ε) → oA δ → oA ε

  -- Δ; x + A ⊢ B+ : type
  oB+ : (δ : Obj) (a : oA δ) → Set
  mB+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) → oB+ δ a → oB+ ε (mA φ a)

  -- Δ; x - A ⊢ B- : type
  oB- : (δ : Obj) (a : oA (~ δ)) → Set
  mB- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) → oB- δ (mA (~m φ) a) → oB- ε a

  -- Δ; x + A, y + B+ ⊢ C++ : type
  oC++ : (δ : Obj) (a : oA δ) (b : oB+ δ a) → Set
  mC++ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB+ δ a) → oC++ δ a b → oC++ ε (mA φ a) (mB+ φ a b)

  -- Δ; x - A, y + B- ⊢ C-+ : type
  oC-+ : (δ : Obj) (a : oA (~ δ)) (b : oB- δ a) → Set
  mC-+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB- δ (mA (~m φ) a)) → oC-+ δ (mA (~m φ) a) b → oC-+ ε a (mB- φ a b)

  -- Δ; x + A, y - B- ⊢ C+- : type
  oC+- : (δ : Obj) (a : oA δ) (b : oB- (~ δ) a) → Set
  mC+- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB- (~ ε) (mA φ a)) → oC+- δ a (mB- (~m φ) a b) → oC+- ε (mA φ a) b

  -- Δ; x - A, y - B+ ⊢ C-- : type
  oC-- : (δ : Obj) (a : oA (~ δ)) (b : oB+ (~ δ) a) → Set
  mC-- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB+ (~ ε) a) → oC-- δ (mA (~m φ) a) (mB+ (~m φ) a b) → oC-- ε a b

  -- Δ; x + A, y + B+, z + C++ ⊢ D+++ : type
  oD+++ : (δ : Obj) (a : oA δ) (b : oB+ δ a) (c : oC++ δ a b) → Set
  mD+++ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB+ δ a) (c : oC++ δ a b)
    → oD+++ δ a b c
    → oD+++ ε (mA φ a) (mB+ φ a b) (mC++ φ a b c)

  -- Δ; x + A, y + B+, z - C-- ⊢ D++- : type
  oD++- : (δ : Obj) (a : oA δ) (b : oB+ δ a) (c : oC-- (~ δ) a b) → Set
  mD++- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB+ δ a) (c : oC-- (~ ε) (mA φ a) (mB+ φ a b))
    → oD++- δ a b (mC-- (~m φ) a b c)
    → oD++- ε (mA φ a) (mB+ φ a b) c

  -- Δ; x + A, y - B-, z + C+- ⊢ D+-+ : type
  oD+-+ : (δ : Obj) (a : oA δ) (b : oB- (~ δ) a) (c : oC+- δ a b) → Set
  mD+-+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB- (~ ε) (mA φ a)) (c : oC+- δ a (mB- (~m φ) a b))
    → oD+-+ δ a (mB- (~m φ) a b) c
    → oD+-+ ε (mA φ a) b (mC+- φ a b c)

  -- Δ; x + A, y - B-, z - C-+ ⊢ D+-- : type
  oD+-- : (δ : Obj) (a : oA δ) (b : oB- (~ δ) a) (c : oC-+ (~ δ) a b) → Set
  mD+-- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA δ) (b : oB- (~ ε) (mA φ a)) (c : oC-+ (~ ε) (mA φ a) b)
    → oD+-- δ a (mB- (~m φ) a b) (mC-+ (~m φ) a b c)
    → oD+-- ε (mA φ a) b c

  -- Δ; x - A, y + B-, z + C-+ ⊢ D-++ : type
  oD-++ : (δ : Obj) (a : oA (~ δ)) (b : oB- δ a) (c : oC-+ δ a b) → Set
  mD-++ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB- δ (mA (~m φ) a)) (c : oC-+ δ (mA (~m φ) a) b)
    → oD-++ δ (mA (~m φ) a) b c
    → oD-++ ε a (mB- φ a b) (mC-+ φ a b c)

  -- Δ; x - A, y + B-, z - C+- ⊢ D-+- : type
  oD-+- : (δ : Obj) (a : oA (~ δ)) (b : oB- δ a) (c : oC+- (~ δ) a b) → Set
  mD-+- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB- δ (mA (~m φ) a)) (c : oC+- (~ ε) a (mB- φ a b))
    → oD-+- δ (mA (~m φ) a) b (mC+- (~m φ) a b c)
    → oD-+- ε a (mB- φ a b) c

  -- Δ; x - A, y - B+, z + C-- ⊢ D--+ : type
  oD--+ : (δ : Obj) (a : oA (~ δ)) (b : oB+ (~ δ) a) (c : oC-- δ a b) → Set
  mD--+ : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB+ (~ ε) a) (c : oC-- δ (mA (~m φ) a) (mB+ (~m φ) a b))
    → oD--+ δ (mA (~m φ) a) (mB+ (~m φ) a b) c
    → oD--+ ε a b (mC-- φ a b c)

  -- Δ; x - A, y - B+, z - C++ ⊢ D--- : type
  oD--- : (δ : Obj) (a : oA (~ δ)) (b : oB+ (~ δ) a) (c : oC++ (~ δ) a b) → Set
  mD--- : {δ ε : Obj} (φ : Mor δ ε)
    (a : oA (~ ε)) (b : oB+ (~ ε) a) (c : oC++ (~ ε) a b)
    → oD--- δ (mA (~m φ) a) (mB+ (~m φ) a b) (mC++ (~m φ) a b c)
    → oD--- ε a b c


tA tB+ tB- tC++ tC-+ tC+- tC--
  tD+++ tD++- tD+-+ tD+--
  tD-++ tD-+- tD--+ tD--- : Set
tA = (c : Obj1) → oA (c , c)
tB+ = (c : Obj1) (a : oA (c , c)) → oB+ (c , c) a
tB- = (c : Obj1) (a : oA (c , c)) → oB- (c , c) a
tC++ = (c : Obj1) → (a : oA (c , c)) (b : oB+ (c , c) a) → oC++ (c , c) a b
tC-+ = (c : Obj1) → (a : oA (c , c)) (b : oB- (c , c) a) → oC-+ (c , c) a b
tC+- = (c : Obj1) → (a : oA (c , c)) (b : oB- (c , c) a) → oC+- (c , c) a b
tC-- = (c : Obj1) → (a : oA (c , c)) (b : oB+ (c , c) a) → oC-- (c , c) a b
tD+++ = (d : Obj1)
    → (a : oA (d , d)) (b : oB+ (d , d) a) (c : oC++ (d , d) a b)
    → oD+++ (d , d) a b c

tD++- = (d : Obj1)
    → (a : oA (d , d)) (b : oB+ (d , d) a) (c : oC-- (d , d) a b)
    → oD++- (d , d) a b c

tD+-+ = (d : Obj1)
    → (a : oA (d , d)) (b : oB- (d , d) a) (c : oC+- (d , d) a b)
    → oD+-+ (d , d) a b c

tD+-- = (d : Obj1)
    → (a : oA (d , d)) (b : oB- (d , d) a) (c : oC-+ (d , d) a b)
    → oD+-- (d , d) a b c

tD-++ = (d : Obj1)
    → (a : oA (d , d)) (b : oB- (d , d) a) (c : oC-+ (d , d) a b)
    → oD-++ (d , d) a b c

tD-+- = (d : Obj1)
    → (a : oA (d , d)) (b : oB- (d , d) a) (c : oC+- (d , d) a b)
    → oD-+- (d , d) a b c

tD--+ = (d : Obj1)
    → (a : oA (d , d)) (b : oB+ (d , d) a) (c : oC-- (d , d) a b)
    → oD--+ (d , d) a b c

tD--- = (d : Obj1)
    → (a : oA (d , d)) (b : oB+ (d , d) a) (c : oC++ (d , d) a b)
    → oD--- (d , d) a b c
