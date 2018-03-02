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

  -- An equational property I expect of the elimination rule.
  -- If you have a (e : (i : #) → S ★ i) and apply it to an endpoint k,
  -- you get the same thing if you ★-eliminate to the head C of the
  -- span, then take the kth arm down to A_k.
  -- Can't seem to orient this as a rewrite in a way that makes agda happy,
  -- so just postulate a path.
  ★elim-eqn : {S : Span} (k : n) (e : (i : #) → S ★ i) →
    e (ι k) == S .f k (★elim e)

  -- The following is a fairly exotic (and probably not fully general)
  -- sequent left rule for #.
  -- The idea is that if you have an (i : #) on the left below the inference
  -- line, you can instead have the proof obligation of
  --   - s : proving the sequent for all endpoints of #
  --   - t : proving the sequent where any assumptions depending on i
  --         are promoted to (b) universally quantified versions of themselves
  --         (the thing I've written here only allows one assumption, but
  --          conceivably the fully general rule allows many)
  --   - ν : these proofs s and t are compatible

  -- Also it is likely this rule is not ok for arbitrary D, but only some
  -- D that are suitably lax/codiscrete/something/etc...
  #left : {B D : # → Set} →
    (s : (k : n) → B (ι k) → D (ι k)) →
    (t : ((j : #) → B j) → (i : #) → D i) →
    (ν : (k : n) (b : (j : #) → B j) → s k (b (ι k)) == t b (ι k)) →
 -- -----------------------------------------------------------
    ((i : #) → B i → D i)

hardRoundTripλ : (p : # → Set) (i : #) → (embu p ★ i) == p i
hardRoundTripλ p i = ua (equiv inj out zig zag) where
  inj : embu p ★ i → p i
  inj = #left (λ _ x → x) ★elim ★elim-eqn i
  out : p i → embu p ★ i
  out = #left (λ _ x → x) ★intro (λ k b → idp) i

  -- I think I need to define some equational properties of #left
  -- before any of this is going to work
  zig : (b : p i) → inj (out b) == b
  zig = {!!}
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
