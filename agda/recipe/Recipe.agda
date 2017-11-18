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
  uatm : {P : Pol} → name → up P

postulate
  rp : Pol → Set -- representation language props,
  rt : Set -- representation language expression types,
  re : rt → Set -- rep'n language expressions

  res : Pol → rt -- the type of 'resources', 'frames' in the rep'n language

  -- internal turnstile
  _▹_ : re (res +) → re (res -) → rp -

  _≥+_ : re (res +) → re (res +) → rp +
  _≥-_ : re (res -) → re (res -) → rp +

  rp∃ : (A : rt) → (re A → rp +) → rp +
  rp∀ : (A : rt) → (re A → rp -) → rp -
  rp∧ : rp + → rp + → rp +
  rp⇒ : rp + → rp - → rp -
  rp↓ : rp - → rp +

cvt : {P : Pol} → lp P → re (res P)
cvt (Lp l⊗ Lp₁) = {!!}
cvt (Lp l⊸ Lp₁) = {!!}

_ⓐ_ : {P : Pol} → up P → lp P → rp +
(Up u⊗ Up₁) ⓐ Lp = {!!}
(Up u⊸ Up₁) ⓐ Lp = {!!}
(uatm n) ⓐ Lp = {!!}


-- ↓ ∀ φ . (N @ φ) ⇒ (r ▹ φ)
-- ↓ ∀ ρ . (P @ ρ) ⇒ (ρ ▹ f)
