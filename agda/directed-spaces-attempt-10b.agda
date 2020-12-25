module directed-spaces-attempt-10b where

data Unit {a} : Set a where
   ⋆ : Unit

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Tr (A : Set1) : (n : ℕ) → Set1 where
  obj : (B : Set) → (B → A) → Tr A zero
  lf : {n : ℕ} → A → Tr A (succ n)
  nd : {n : ℕ} → Tr (Tr A (succ n)) n → Tr A (succ n)
