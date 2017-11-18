module Recipe where

{- Trying to nail down the "Logical Recipes" approach,
   in order to see how it generalizes to the dependent case. -}

-- WARNING: bogus HOAS throughout

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

data rs : Set -- representation language first-order sorts
data rt : rs → Set -- rep'n language terms

data rs where
  $lp : Pol → rs -- the sort of 'resources', 'frames' in the rep'n language
  $lt : rt ($lp +) → rs -- the sort of 'proofs' of those things?
  _⇀_ : rs → rs → rs

data rt where
  ⋆ : {σ : Pol} → lp σ → rt ($lp σ)
  lam : {ρ : lp +} → (lt ρ → lp +) → rt ($lt (⋆ ρ) ⇀ $lp +)

_rt⊗_ : rt ($lp +) → rt ($lp +) → rt ($lp +)
(⋆ x) rt⊗ (⋆ y) = ⋆ (x l⊗ y)
_rt⊸_ : rt ($lp +) → rt ($lp -) → rt ($lp -)
(⋆ x) rt⊸ (⋆ y) = ⋆ (x l⊸ y)
rtΣ : (ρ : rt ($lp +)) → rt ($lt ρ ⇀ $lp +) → rt ($lp +)
rtΣ (⋆ x) (lam y) = ⋆ (lΣ x y)

data rp : Pol → Set where -- representation language props,
  _≥+_ : rt ($lp +) → rt ($lp +) → rp +
  _≥-_ : rt ($lp -) → rt ($lp -) → rp +
  -- internal turnstile
  _▹_ : rt ($lp +) → rt ($lp -) → rp -

  r∃ : {s : rs} → (rt s → rp +) → rp +
  r∀ : {s : rs} → (rt s → rp -) → rp -

  _r∧_ : rp + → rp + → rp +
  _r⇒_ : rp + → rp - → rp -
  r↓ : rp - → rp +
  ratm : name → (σ : Pol) → rt ($lp σ) → rp +
infixr 20 _r∧_

{- this seems to be the crux for generalizing to the dependent case -}
postulate
  _ⓑ_ : {P : up +} (Q : ut P → up +) {ρ : rt ($lp +)} (θ : rt ($lt ρ ⇀ $lp +)) → rp +

_ⓐ_ : {σ : Pol} → up σ → rt ($lp σ) → rp +
(P u⊗ Q) ⓐ r = r∃ λ ρ → r∃ λ θ → (r ≥+ (ρ rt⊗ θ)) r∧ (P ⓐ ρ) r∧ (Q ⓐ θ)
(uΣ P Q) ⓐ r = r∃ { $lp + } λ ρ →  r∃ { ($lt ρ) ⇀ ($lp +) } λ θ →
  (r ≥+ rtΣ ρ θ) r∧ (P ⓐ ρ) r∧ (Q ⓑ θ)
(P u⊸ N) ⓐ f = r∃ λ ρ → r∃ λ φ → (φ ≥- (ρ rt⊸ f)) r∧ (P ⓐ ρ) r∧ (N ⓐ φ)
-- (↓ N) @ r = ↓ ∀ φ . (N @ φ) ⇒ (r ▹ φ)
-- (↑ P) @ f = ↓ ∀ ρ . (P @ ρ) ⇒ (ρ ▹ f)
(u↓ N) ⓐ r = r↓ (r∀ (λ φ → (N ⓐ φ) r⇒ (r ▹ φ)))
(u↑ P) ⓐ f = r↓ (r∀ (λ ρ → (P ⓐ ρ) r⇒ (ρ ▹ f)))
(uatm σ n) ⓐ rf = ratm n σ rf

-- Γ ←→ P : up +
-- Γ ⊢ A ←→ Q : ut P → up +
-- γ ⊢ α ←→ θ : rt ($lt ρ ⇀ $lp +)
