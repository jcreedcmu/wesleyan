{-# OPTIONS --without-K --rewriting #-}
module Parametricity where

-- This agda file contains my understanding/reconstruction/digestion of the ideas in
-- "A Presheaf Model of Parametric Type Theory" (Bernardy, Coquand, Moulin, 2015)
-- and Moulin's thesis
-- "Internalizing Parametricity"
-- http://publications.lib.chalmers.se/records/fulltext/235758/235758.pdf

open import HoTT hiding ( O; Path; _*_ ; !)
-- (https://github.com/HoTT/HoTT-Agda)

postulate
  -- There exists an interval type with an endpoint 'O'
  𝕀 : Set
  O : 𝕀

  -- The type
  --     Path (λ i → A) a
  -- is what Bernardy-Coquand-Moulin write as
  --     A ∋ᵢ a
  -- and Moulin in his thesis writes as
  --     ∀i.A ∋ a
  -- and is here called 'Path' because it's analogous to path types (with
  -- fixed endpoints) in, e.g., HoTT or cubical type theories --- the
  -- difference being that here we have one endpoint instead of two.
  -- It's a subtype of ∀i.A, the one restricted to terms M : ∀i.A such
  -- that M O = a.
  Path : ∀ {ℓ} (A : 𝕀 → Set ℓ) (a : A O) → Set ℓ

  -- We declare a form of application for path types...
  _*_ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O}
    → Path A a → (i : 𝕀) → A i

  -- ...and an abstraction.
  lam : ∀ {ℓ} {A : 𝕀 → Set ℓ} (f : (i : 𝕀) → A i)
    → Path A (f O)

  -- Conveniently, agda lets us postulate reductions, so we say that
  -- when M has type A ∋ᵢ a, and we apply it to O, we have that M O is
  -- *definitionally* equal to a.
  O-rewrite : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O}
    (p : Path A a) → (p * O) ↦ a
  {-# REWRITE O-rewrite #-}

  -- Similarly, we have β-reduction and η-contraction as definitional equalities.
  β-rewrite : ∀ {ℓ} {A : 𝕀 → Set ℓ} (F : (i : 𝕀) → A i) (j : 𝕀)
    → (lam F * j) ↦ F j
  {-# REWRITE β-rewrite #-}

  η-rewrite : ∀ {ℓ} {A : 𝕀 → Set ℓ} {a : A O}
    (R : Path A a) → lam (λ j → R * j) ↦ R
  {-# REWRITE η-rewrite #-}

-- Syntactic sugar for path types. I prefer reading the endpoint on
-- the left for some reason. The 'i' position is binding.
syntax Path (λ i -> A) a = a ∈ i · A

-- Having set things up this way means that we don't need to specially
-- declare things like BCM's operations ⦇ , ⦈ and ! --- they're merely
-- definable ways to convert between the types a ∈ i · A and ∀i.A.
-- (cf. Moulin's thesis, p88, rules PARAM and IN-ABS)
module _ where
  -- although, to be fair, as you can see below, ! basically *is* the
  -- lambda abstraction we declared for path types, and ⦅_,_⦆ is the
  -- corresponding application. In that way, I'm not really getting a
  -- free lunch --- but I think it's clearer/more natural to see them
  -- as lambda abstraction and application, rather than some ad hoc
  -- things.
  _! : ∀ {ℓ} {A : 𝕀 → Set ℓ} (u : (i : 𝕀) → A i) → u O ∈ i · (A i)
  _! = lam

  ⦅_,_⦆ : {A : 𝕀 → Set} (a : A O) (p : a ∈ i · A i) → ((i : 𝕀) → A i)
  ⦅_,_⦆ a p i = p * i

  -- Several of the conversion-relation axioms fall out of these definitions:
  -- (cf. Moulin's thesis, p89)
  PAIR-ORIG : {A : 𝕀 → Set} (a : A O) (p : a ∈ i · A i) →
    ⦅ a , p ⦆ O == a
  PAIR-ORIG a p = idp

  PAIR-PARAM : {A : 𝕀 → Set} (a : A O) (p : a ∈ i · A i) →
    (⦅ a , p ⦆ !) == p
  PAIR-PARAM a p = idp

  SURJ-PARAM : {A : 𝕀 → Set} (u : (i : 𝕀) → A i) →
    ⦅ u O , u ! ⦆ == u
  SURJ-PARAM u = idp

-- -----------------------------

-- Then I make the somewhat more speculative conjecture that the
-- remainder of BCM's axiomatization of how their types behave amounts
-- to asserting that two particular functions are equivalences.

-- (1) embu, an "EMBedding function for the Universe". It is the case
-- that if we have a path p in the universe Set whose endpoint is A,
-- then we have a relation on A. A 'relation on A' means here a
-- proof-relevant relation, i.e. a function A → Set.

--   The relation for p is, given an a, and a point i in the interval,
-- the set of all possible paths in the type p at the point i, whose
-- endpoint is a.
embu : ∀ {ℓ} {A : Set ℓ} (p : A ∈ i · Set ℓ)
  (a : A) → Set ℓ
embu {ℓ} {A} p a = a ∈ i · (p * i)

--   To assert the existence of an inverse of embu is to say that
-- from *any* relation on the set A, we can find a corresponding path
-- in the universe.

postulate
  embu-equiv : ∀ {ℓ} {A : Set ℓ} → is-equiv (embu {ℓ} {A})

module _ where
  -- This inverse is the Ψ_A used in rule IN-PRED (cf. Moulin's thesis, p88)
  Ψ : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) → A ∈ i · Set ℓ
  Ψ P = embu-equiv .is-equiv.g P

-- (2) embf, an "EMBedding function for Function extensionality".
-- Suppose we have two interval-varying types A and B, such that B is
-- also fibered over A. Suppose we have a path in Π (A i) (B i) whose
-- endpoint let's call t.

-- Then we can construct a dependent function that takes an A-path x
-- and yields a B-path, such that that B-path's endpoint is always t(x
-- O). Here's how:
embf : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
     {t : (x : A O) → B O x}
     → (t ∈ i · Π (A i) (B i))
     → ((x : (i : 𝕀) → A i) → (t (x O)) ∈ i · B i (x i))
embf p x = lam (λ i → (p * i) (x i))

-- To assert the existence of an inverse of embf is to assert that a
-- form of dependent function extensionality holds.

postulate
  embf-equiv : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
    {f : (x : A O) → B O x}
    → is-equiv (embf {ℓ} {A} {B} {f})

module _ where
  -- This inverse is the Φ_t used in rule IN-FUN (cf. Moulin's thesis, p88)
  Φ : ∀ {ℓ} {A : 𝕀 → Set ℓ} {B : (i : 𝕀) (x : A i) → Set ℓ}
    → (t : (x : A O) → B O x)
    → (u : (x : (i : 𝕀) → A i) → (t (x O)) ∈ i · B i (x i))
    → t ∈ i · ((x : A i) → B i x)
  Φ t u = embf-equiv .is-equiv.g u

-- (I conjecture SURJ-TYPE, SURJ-FUN, PAIR-PRED, and PAIR-APP are
-- provable using the round-trip properties of equivalences but
-- haven't got around to formalizing it yet.)
