{-# OPTIONS --without-K --rewriting #-}
module Coglue2 {n : Set} where

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

-- Just doing the nondependent version for now
record Pkg (B D : # → Set) : Set where
  field
    s : (k : n) (b : B (ι k)) → D (ι k)
    t : (b : (j : #) → B j) → (i : #) → D i
    ν : (k : n) (b : (j : #) → B j) → s k (b (ι k)) == t b (ι k)

Fpath : (B D : # → Set) → Set
Fpath B D = (i : #) (b : B i) → D i

mkPkg : {B D : # → Set} → Fpath B D → Pkg B D
mkPkg fp = record {
  s = λ k b → fp (ι k) b ;
  t = λ b i → fp i (b i) ;
  ν = λ k b → idp }

postulate
  #left-equiv : {B D : # → Set} → is-equiv (mkPkg {B} {D})

#left : {B D : # → Set} → Pkg B D → Fpath B D
#left {B} {D} p = #left-equiv .is-equiv.g p

general-lemma : {sh : Set} {B1 B2 B3 : sh → Set}
  {K1 K2 : (B1 B2 : sh → Set) → Set}
  (mk : {B1 B2 : sh → Set} → K1 B1 B2 → K2 B1 B2)
  → (eq : {B1 B2 : sh → Set} → is-equiv (mk {B1} {B2}))
  → (μ1 : K1 B1 B2 → K1 B2 B3 → K1 B1 B3)
  → (μ2 : K2 B1 B2 → K2 B2 B3 → K2 B1 B3)
  → (commute : (y12 : K1 B1 B2) (y23 : K1 B2 B3) →
             mk (μ1 y12 y23) ==
             μ2 (mk y12) (mk y23))
  → (x12 : K2 B1 B2) (x23 : K2 B2 B3)
    → μ1 (eq .is-equiv.g x12) (eq .is-equiv.g x23) ==
    eq .is-equiv.g (μ2 x12 x23)
general-lemma {sh} {B1} {B2} {B3} {K1} mk eq μ1 μ2 commute x12 x23 =
  expr
  =⟨ ! (eq .g-f expr) ⟩
  eq .g (mk expr)
  =⟨ ap (eq .g) subgoal ⟩
  eq .g (μ2 x12 x23)
  =∎ where
  open is-equiv
  expr : K1 B1 B3
  expr = μ1 (eq .g x12) (eq .g x23)
  subgoal : mk expr == μ2 x12 x23
  subgoal = mk expr
    =⟨ commute ( (eq .g x12)) ( (eq .g x23)) ⟩
    μ2 (mk (eq .g x12)) (mk (eq .g x23))
    =⟨ ap2 μ2 (eq .f-g x12) (eq .f-g x23) ⟩
    μ2 x12 x23
    =∎

FpathFunc : {B D F : # → Set} → Fpath B D → Fpath D F → Fpath B F
FpathFunc π1 π2 = λ i b → π2 i (π1 i b) -- violation of affineness???

PkgFunc : {B D F : # → Set} → Pkg B D → Pkg D F → Pkg B F
PkgFunc
  record { s = s1 ; t = t1 ; ν = ν1 }
  record { s = s2 ; t = t2 ; ν = ν2 } =
  record {
    s = λ k b → s2 k (s1 k b) ;
    t = λ b i → t2 (λ j → t1 b j) i ;
    ν = λ k b → ap (λ z → s2 k z) (ν1 k b) ∙ ν2 k (t1 b) }

specific-lemma : {B D F : # → Set} →
      (pack1 : Pkg B D) (pack2 : Pkg D F) →
      FpathFunc (#left pack1) (#left pack2) == #left (PkgFunc pack1 pack2)
specific-lemma {B} {D} {F} =
  general-lemma {#} {B} {D} {F} {Fpath} {Pkg}
   mkPkg #left-equiv FpathFunc PkgFunc (λ y12 y23 → idp)

-- Some more lemmas
★elim-eqn-lem : {S : Span} (e : (i : #) → S ★ i) (i : #)→
  e i == ★intro {S} (★elim e) i
★elim-eqn-lem {S} e i = idp

★elim-eqn : {S : Span} (k : n) (e : (i : #) → S ★ i) →
  e (ι k) == S .f k (★elim e)
★elim-eqn {S} k e = ★elim-eqn-lem {S} e (ι k)

hardRoundTripλ : (p : # → Set) (i : #) → (embu p ★ i) == p i
hardRoundTripλ p i = ua (equiv inj out zig zag) where
  injPack : Pkg (λ i → embu p ★ i) p
  injPack = record {
    s = (λ _ x → x) ;
    t = ★elim ;
    ν = ★elim-eqn }
  outPack : Pkg p (λ i → embu p ★ i)
  outPack = record {
    s = λ _ x → x ;
    t = ★intro ;
    ν = λ k b → idp }
  inj : embu p ★ i → p i
  inj = #left injPack i
  out : p i → embu p ★ i
  out = #left outPack i

  zig : (b : p i) → inj (out b) == b
  zig b =
    inj (out b)
    =⟨ app= (app= (specific-lemma outPack injPack) i) b  ⟩
    #left (PkgFunc outPack injPack) i b
    =⟨ idp ⟩
    #left (mkPkg λ i' b' → b') i b
    =⟨ app= (app= (#left-equiv .is-equiv.g-f (λ i' b' → b')) i) b ⟩
    (λ (i' : #) (b' : p i) → b') i b
    =⟨ idp  ⟩
    b =∎

  zag : (a : embu p ★ i) → out (inj a) == a
  zag a = out (inj a)
    =⟨ app= (app= (specific-lemma injPack outPack) i) a ⟩
    #left (PkgFunc injPack outPack) i a
    =⟨ idp ⟩
    #left (mkPkg λ i' a' → a') i a
    =⟨ app= (app= (#left-equiv .is-equiv.g-f (λ i' a' → a')) i) a  ⟩
    (λ (i' : #) (a' : embu p ★ i) → a') i a
    =⟨ idp ⟩
    a =∎

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
