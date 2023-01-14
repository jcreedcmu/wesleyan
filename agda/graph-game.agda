open import Agda.Primitive

data ⊤ {a} : Set a where
 ⋆ : ⊤

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

_×_ : (A : Set) (B : Set) → Set
A × B = Σ A (λ _ → B)

square : (A : Set) → Set
square A = A × A

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

E : ℕ → Set₁
D : (n : ℕ) → E n → Set₁

E zero = ⊤
E (succ x) = Σ (E x) (λ e → D x e → Set)

D zero ⋆ = ⊤
D (succ x) (e , B) = Σ (D x e) B

T : (n : ℕ) (k : E n → Set₁) → Set₁
T zero k = k ⋆
T (succ n) k = T n (λ e → (C : D n e → Set) → Σ (D n e → Set) (λ B → k (e , B)))

module _ (C₀ : Set) (C₁ : C₀ → C₀ → Set) where
  data path  : C₀ → C₀ → Set where
    id : (c : C₀) → path c c
    cons : (c d e : C₀) → path c d → C₁ d e → path c e

{-
What's going on here is the conversation:
Alice: What are the objects C₀ : Set?
Bob: Here's C₀.
Alice: Ok, I've decided boundaries of 1-cells are B₁ = C₀².
       What are the morphisms C₁ : C₀² → Set?
Bob: Here's C₁.
Alice: Ok, I've decided boundaries of 2-cells are pairs of paths in C₁.
-}
sample : T (succ (succ zero)) (λ _ → ⊤)
sample = λ C₀ → (λ _ → square (C₀ ⋆)) , λ C₁ → (λ (_ , (dom , cod)) → square (path (C₀ ⋆) (λ dom cod → C₁ (⋆ , (dom , cod))) dom cod)) , ⋆
