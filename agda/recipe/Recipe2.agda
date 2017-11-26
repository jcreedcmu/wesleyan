module Recipe2 where

open import HoTT using ( _×_ ; Σ ; _,_ )

{- Trying to nail down the "Logical Recipes" approach for the case of linear logic,
  to make sure I know what I'm doing. -}

-- WARNING: bogus HOAS throughout

data Pol : Set where
  + – : Pol -- <- that's a dash (\en) not a ascii minus sign, so that
            -- I can do –} without it being a comment.

postulate
  name : Set

data lp : Pol → Set -- 'lower' types
postulate
  _l≤_ : {σ : Pol} → lp σ → lp σ → Set
  ls : Set
  _◃_ : lp + → lp – → ls
  _⊴_  : ls → ls → Set
  l≤refl  : {σ : Pol} {X : lp σ} → X l≤ X
  l≤trans  : {σ : Pol} {X Y Z : lp σ} → X l≤ Y → Y l≤ Z → X l≤ Z
  ⊴refl  : {X : ls} → X ⊴ X
  ⊴trans  : {X Y Z : ls} → X ⊴ Y → Y ⊴ Z → X ⊴ Z
  is : ls → Set

holds : ls → Set
holds s = (t : ls) → s ⊴ t → is t -- XXX: 50% chance I have the orientation of s ⊴ t backwards

mkholds : {X Y : ls} → (X ⊴ Y) → holds X → holds Y
mkholds leq h t leq' = h t (⊴trans leq leq')

data lp where
  𝟙 : lp +
  _l⊗_ : lp + → lp + → lp +
  _l⊸_ : lp + → lp – → lp –

_≜_ : ls → ls → Set
X ≜ Y = (X ⊴ Y) × (Y ⊴ X)

_≡_ : {σ : Pol} → lp σ → lp σ → Set
X ≡ Y = (X l≤ Y) × (Y l≤ X)

postulate
  adj : {x y : lp +} {z : lp –} → (x ◃ (y l⊸ z)) ≜ ((x l⊗ y) ◃ z)
  assoc : {x y z : lp +} → (x l⊗ (y l⊗ z)) ≡ ((x l⊗ y) l⊗ z)
  commute : {x y : lp +} → (x l⊗ y) ≡ (y l⊗ x)
  unit : {x : lp +} → (x l⊗ 𝟙) ≡ x
  ⊗cong : {x x' y y' : lp +} → (x l≤ x') → (y l≤ y') → ((x l⊗ y) l≤ (x' l⊗ y'))
  ⊸cong : {x x' : lp +} {y y' : lp –} → (x l≤ x') → (y l≤ y') → ((x l⊸ y) l≤ (x' l⊸ y'))
  ◃cong : {x x' : lp +} {y y' : lp –} → (x l≤ x') → (y l≤ y') → ((x ◃ y) ⊴ (x' ◃ y'))
  μ : {x : lp +} → ((x l⊗ x) l≤ x)
  η : {x : lp +} → (𝟙 l≤ x)

up : Pol → Set₁ -- 'upper' props

up σ = lp σ → Set

_⊗_ : up + → up + → up +
_⊗_ P₁ P₂ r = Σ (lp +) (λ α₁ → Σ (lp +) (λ α₂ → ((α₁ l⊗ α₂) l≤ r) × P₁ α₁ × P₂ α₂))

_⊸_ : up + → up – → up –
_⊸_ P N f = Σ (lp +) (λ α → Σ (lp –) (λ φ → ((α l⊸ φ) l≤ f) × P α × N φ))

↑ : up + → up –
↑ P f = (α : lp +) → (P α) → holds (α ◃ f)

↓ : up – → up +
↓ N r = (φ : lp –) → (N φ) → holds (r ◃ φ)

_⊢_ : up + → up – → Set
P ⊢ N = (α : lp +) (φ : lp –) → P α → N φ → holds (α ◃ φ)

thm : (a : up +) → a ⊢ ↑ (a ⊗ a)
thm a α φ x y = mkholds (◃cong μ l≤refl) (y (α l⊗ α) (α , α , l≤refl , (x , x)))
