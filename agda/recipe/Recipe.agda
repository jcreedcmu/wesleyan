module Recipe where

{- Trying to nail down the "Logical Recipes" approach,
   in order to see how it generalizes to the dependent case. -}

data Pol : Set where
  + - : Pol

postulate
  name : Set

data lp : Pol → Set -- 'lower' props
data lt : lp + → Set -- 'lower' terms

data lp where
  _l⊗_ : lp + → lp + → lp +
  lΣ : (A : lp +) → (lt A → lp +) → lp +
  _l⊸_ : lp + → lp - → lp -
data lt where

data up : Pol → Set -- 'upper' props
data ut : up + → Set -- 'upper' terms

data up where
  _u⊗_ : up + → up + → up +
  uΣ : (A : up +) → (ut A → up +) → up +
  _u⊸_ : up + → up - → up -
  u↑ : up + → up -
  u↓ : up - → up +
  uatm : (σ : Pol) → name → up σ
data ut where

data rs : Set where -- representation language first-order sorts
  res : Pol → rs -- the sort of 'resources', 'frames' in the rep'n language

data rt : rs → Set where -- rep'n language terms
  ⋆ : {σ : Pol} → lp σ → rt (res σ)

_rt⊗_ : rt (res +) → rt (res +) → rt (res +)
(⋆ x) rt⊗ (⋆ y) = ⋆ (x l⊗ y)
_rt⊸_ : rt (res +) → rt (res -) → rt (res -)
(⋆ x) rt⊸ (⋆ y) = ⋆ (x l⊸ y)

data rp : Pol → Set where -- representation language props,
  _≥+_ : rt (res +) → rt (res +) → rp +
  _≥-_ : rt (res -) → rt (res -) → rp +
  -- internal turnstile
  _▹_ : rt (res +) → rt (res -) → rp -

  -- warning, bogus HOAS:
  r∃ : {s : rs} → (rt s → rp +) → rp +
  r∀ : {s : rs} → (rt s → rp -) → rp -

  _r∧_ : rp + → rp + → rp +
  _r⇒_ : rp + → rp - → rp -
  r↓ : rp - → rp +
  ratm : name → (σ : Pol) → rt (res σ) → rp +
infixr 20 _r∧_

_ⓐ_ : {σ : Pol} → up σ → rt (res σ) → rp +
(P u⊗ Q) ⓐ r = r∃ λ ρ → r∃ λ θ → (r ≥+ (ρ rt⊗ θ)) r∧ (P ⓐ ρ) r∧ (Q ⓐ θ)
(uΣ P Q) ⓐ r = {!!}
(P u⊸ N) ⓐ f = r∃ λ ρ → r∃ λ φ → (φ ≥- (ρ rt⊸ f)) r∧ (P ⓐ ρ) r∧ (N ⓐ φ)
-- (↓ N) @ r = ↓ ∀ φ . (N @ φ) ⇒ (r ▹ φ)
-- (↑ P) @ f = ↓ ∀ ρ . (P @ ρ) ⇒ (ρ ▹ f)
(u↓ N) ⓐ r = r↓ (r∀ (λ φ → (N ⓐ φ) r⇒ (r ▹ φ)))
(u↑ P) ⓐ f = r↓ (r∀ (λ ρ → (P ⓐ ρ) r⇒ (ρ ▹ f)))
(uatm σ n) ⓐ rf = ratm n σ rf
