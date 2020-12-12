module directed-spaces-attempt-5 where

postulate
  𝕀 : Set -- closed interval [0,1]
  ℍ : 𝕀 → Set -- right half of interval starting at argument
    -- i.e. ℍ 0.75 = [0.75, 1]
  ι : {i : 𝕀} → ℍ i → 𝕀 -- inclusion

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record ConSpace : Set₁ where
  constructor conspace
  field
    {X} : Set
    β : X → 𝕀
    p : (x : X) → ℍ (β x)

    {- lifting -}
    h : (x : X) → ℍ (β x) → X

  prop1 : (x : X) (k : ℍ (β x) → X) → Set
  prop1 x k = k (p x) ≡ x

  prop2 : (x : X) (k : ℍ (β x) → X) → Set
  prop2 x k = (z : ℍ (β x)) → ι (p (k z)) ≡ ι z

  field
    has-prop1 : (x : X) → prop1 x (h x)

    has-prop2 : (x : X) → prop2 x (h x)

    η : (x : X) (k : ℍ (β x) → X) →
      prop1 x k → prop2 x k → k ≡ h x
