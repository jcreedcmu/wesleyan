module Recipe where

{- Trying to nail down the "Logical Recipes" approach,
   in order to see how it generalizes to the dependent case. -}

data Pol : Set where
  + - : Pol

postulate
  name : Set

data lp : Pol → Set where -- 'lower' props
  _l⊗_ : lp + → lp + → lp +
  _l⊸_ : lp + → lp - → lp -

data up : Pol → Set where -- 'upper' props
  _u⊗_ : up + → up + → up +
  _u⊸_ : up + → up - → up -
  u↑ : up + → up -
  u↓ : up - → up +
  uatm : (σ : Pol) → name → up σ


{- I thought about having
      rt : Set -- representation language expression types,
      re : rt → Set -- rep'n language expressions
      res : Pol → rt -- the type of 'resources', 'frames' in the rep'n language
   and quantifiers
      rp∃ : (A : rt) → (re A → rp +) → rp +
      rp∀ : (A : rt) → (re A → rp -) → rp -
   and a function
      cvt : {σ : Pol} → lp σ → re (res σ)
   converting from lower props to term expressions, but I thought
   it might be simpler just to identify lp with re ∘ res
-}

data rp : Pol → Set where -- representation language props,
  _≥+_ : lp + → lp + → rp +
  _≥-_ : lp - → lp - → rp +
  -- internal turnstile
  _▹_ : lp + → lp - → rp -

  -- warning, bogus HOAS:
  r∃ : {σ : Pol} → (lp σ → rp +) → rp +
  r∀ : {σ : Pol} → (lp σ → rp -) → rp -

  _r∧_ : rp + → rp + → rp +
  _r⇒_ : rp + → rp - → rp -
  r↓ : rp - → rp +
  ratm : name → (σ : Pol) → lp σ → rp +
infixr 20 _r∧_

_ⓐ_ : {σ : Pol} → up σ → lp σ → rp +
(P u⊗ Q) ⓐ r = r∃ λ ρ → r∃ λ θ → (r ≥+ (ρ l⊗ θ)) r∧ (P ⓐ ρ) r∧ (Q ⓐ θ)
(P u⊸ N) ⓐ f = r∃ λ ρ → r∃ λ φ → (φ ≥- (ρ l⊸ f)) r∧ (P ⓐ ρ) r∧ (N ⓐ φ)
-- (↓ N) @ r = ↓ ∀ φ . (N @ φ) ⇒ (r ▹ φ)
-- (↑ P) @ f = ↓ ∀ ρ . (P @ ρ) ⇒ (ρ ▹ f)
(u↓ N) ⓐ r = r↓ (r∀ (λ φ → (N ⓐ φ) r⇒ (r ▹ φ)))
(u↑ P) ⓐ f = r↓ (r∀ (λ ρ → (P ⓐ ρ) r⇒ (ρ ▹ f)))
(uatm σ n) ⓐ rf = ratm n σ rf
