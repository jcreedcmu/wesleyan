{-# OPTIONS --without-K --rewriting #-}
module Coglue {n : Set} where

open import HoTT hiding (Span ; S ; span=)

postulate
  # : Set
  ι : n → #

record Span : Set₁ where
  constructor span
  field
    C : Set
    A : n → Set
    f : (k : n) → C → A k
open Span

--       C     <- head of the span
--   f1/   \fn
--    v     v    <- arms of the span
--   A1 ... An

-- We know how to canonically turn a path in the universe into a relation
embu : (# → Set) → Span
embu p = span ((i : #) → p i) (λ k → p (ι k)) (λ k c → c (ι k))

postulate
  -- We postulate a way of turning relations into paths,
  -- a putative inverse of embu:
  _★_ : Span → (# → Set)

  -- When the second argument is an endpoint of #,
  -- this type reduces to one of the arm types of the span
  ★-rewrite : (S : Span) (k : n)
    → (S ★ (ι k)) ↦ (S .A k)
  {-# REWRITE ★-rewrite #-}

  -- Intro and elim rules
  ★intro : {S : Span} (c : S .C) (i : #) → S ★ i
  ★elim : {S : Span} (e : (i : #) → S ★ i) → S .C

  ★-β-reduction : {S : Span} (c : S .C) → ★elim {S} (★intro {S} c) ↦ c
  {-# REWRITE ★-β-reduction #-}

  ★-η-reduction : {S : Span} (ℓ : (i : #) → S ★ i) → ★intro {S} (★elim {S} ℓ) ↦ ℓ
  {-# REWRITE ★-η-reduction #-}

  -- An introduction form at an endpoint reduces to one of the arms of
  -- the span applied to c.
  ★intro-rewrite : {S : Span} (c : S .C) (k : n)
    → ★intro {S} c (ι k) ↦ S .f k c
  {-# REWRITE ★intro-rewrite #-}


record Pkg (B : # → Set) (D : (j : #) → B j → Set) : Set where
  field
    s : (k : n) (b : B (ι k)) → D (ι k) b
    t : (b : (j : #) → B j) → (i : #) → D i (b i)
    ν : (k : n) (b : (j : #) → B j) → s k (b (ι k)) == t b (ι k)

nonDep : ({B} D : # → Set) →  (j : #) → B j → Set
nonDep D = (λ i b → D i)

PkgNd : (B D : # → Set) → Set
PkgNd B D = Pkg B (nonDep D)

Fpath : (B : # → Set) (D : (j : #) → B j → Set) → Set
Fpath B D = (i : #) (b : B i) → D i b

mkPkg : {B : # → Set} {D : (j : #) → B j → Set} → Fpath B D → Pkg B D
mkPkg fp = record {
  s = λ k b → fp (ι k) b ;
  t = λ b i → fp i (b i) ;
  ν = λ k b → idp }

postulate
  #dleft : {B : # → Set} {D : (j : #) → B j → Set}
    → is-equiv (mkPkg {B} {D})

--   -- these exchange rules are appropriately surjective
--   surj-#dleft : {B : # → Set} {D : (j : #) → B j → Set} →
--     (t : Fpath B D) → t == #dleft (mkPkg t)

-- -- Nondependent version of surj-#left
-- surj-#left : {B D : # → Set} →
--   (t : Fpath B (λ i b → D i)) →
--   t == #left (mkPkg t)
-- surj-#left = surj-#dleft

-- Nondependent version of #dleft
#left : {B D : # → Set} → PkgNd B D → Fpath B (nonDep D)
#left {B} {D} p = #dleft .is-equiv.g p

functorial : {B D F : # → Set} → PkgNd B D → PkgNd D F → PkgNd B F
functorial
  record { s = s1 ; t = t1 ; ν = ν1 }
  record { s = s2 ; t = t2 ; ν = ν2 } =
  record {
    s = λ k b → s2 k (s1 k b) ;
    t = λ b i → t2 (λ j → t1 b j) i ;
    ν = λ k b → ap (λ z → s2 k z) (ν1 k b) ∙ ν2 k (t1 b) }

-- Some more lemmas
★elim-eqn-lem : {S : Span} (e : (i : #) → S ★ i) (i : #)→
  e i == ★intro {S} (★elim e) i
★elim-eqn-lem {S} e i = idp

★elim-eqn : {S : Span} (k : n) (e : (i : #) → S ★ i) →
  e (ι k) == S .f k (★elim e)
★elim-eqn {S} k e = ★elim-eqn-lem {S} e (ι k)

hardRoundTripλ : (p : # → Set) (i : #) → (embu p ★ i) == p i
hardRoundTripλ p i = ua (equiv inj out zig zag) where
  inj : embu p ★ i → p i
  inj = #left (record {
    s = (λ _ x → x) ;
    t = ★elim ;
    ν = ★elim-eqn }) i
  out : p i → embu p ★ i
  out = #left (record {
    s = λ _ x → x ;
    t = ★intro ;
    ν = λ k b → idp }) i

  -- I think I need to define some equational properties of #left
  -- before any of this is going to work
  zig : (b : p i) → inj (out b) == b
  zig b = {!!}
  zag : (a : embu p ★ i) → out (inj a) == a
  zag = {!!}

hardRoundTrip : (p : # → Set) → _★_ (embu p) == p
hardRoundTrip p = λ= (hardRoundTripλ p)

ertCe : (S : Span) → embu (_★_ S) .C ≃ S .C
ertCe S = (equiv inj out (λ _ → idp) (λ _ → idp)) where
  inj : embu (_★_ S) .C → S .C
  inj = ★elim
  out : S .C → embu (_★_ S) .C
  out = ★intro

ertC : (S : Span) → embu (_★_ S) .C == S .C
ertC S = ua (ertCe S)

ertA : (S : Span) → embu (_★_ S) .A == S .A
ertA S = idp

span=lem : {S T : Span} (p : S .C == T .C) (q : S .A == T .A) →
  (λ k c → coe (app= q k) (S .f k c)) == (λ k c → T .f k (coe p c))
  → S == T
span=lem idp idp idp = idp

span= : {S T : Span} (p : S .C == T .C) (q : S .A == T .A) →
  ((k : n) (c : S .C) → coe (app= q k) (S .f k c) == T .f k (coe p c))
  → S == T
span= p q z = span=lem p q (λ= (λ k -> λ= (λ c → z k c)))

ertF : (S : Span) (k : n) (c : (i : #) → S ★ i) →
  c (ι k) == f S k (coe (ertC S) c)
ertF S k c = ★elim-eqn k c ∙ ap (f S k) (! (coe-β (ertCe S) c))

easyRoundTrip : (S : Span) → embu (_★_ S) == S
easyRoundTrip S = span= (ertC S) (ertA S) (ertF S)

-- --------------------
-- Can characterize paths in the universe as spans:

pathsInSetAreSpans : (# → Set) == Span
pathsInSetAreSpans = ua (equiv embu (_★_) easyRoundTrip hardRoundTrip)
