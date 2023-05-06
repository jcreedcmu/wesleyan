open import Agda.Primitive

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ {a} {b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

postulate
 pushout : ∀ {a} (A B C : Set a) (f : A → B) (g : A → C) → Set a

data Unit {a} : Set a where
   ⋆ : Unit

data Zero {a} : Set a where

abort : ∀ {a b} {A : Set a} → Zero {b} → A
abort ()

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{---- Stage 1a: declare the big knot -----------------}

sphereT : (n : ℕ) → Set₁
sphere : (n : ℕ) → sphereT n → Set₁
record path (n : ℕ) (b : sphereT n) : Set₁
record realize (n : ℕ) (b : sphereT n) (p1 p2 : path n b) (ρ : Set) : Set
realizeT : (n : ℕ) (b : sphereT n) (ρ : Set) → Set

{---- Stage 1b: define the big knot -----------------}

record path n b where
 pattern
 field
  t : Set
  f : realizeT n b t
open path

sphere n b = path n b × path n b
sphereT zero = Unit
sphereT (succ n) = Σ (sphereT n) (λ s → sphere n s)

record realize n b p1 p2 ρ where
 constructor mkrel
 field
  f1 : p1 .t → ρ
  f2 : p2 .t → ρ

realizeT zero b ρ = Unit
realizeT (succ n) (b , (p1 , p2)) ρ = realize n b p1 p2 ρ

{---- Stage 2: composition -----------------}

_∙_ : {n : ℕ} {ρ ρ' : Set} {b : sphereT n} {p1 : path n b} {p2 : path n b} (r : realize n b p1 p2 ρ) (f : ρ → ρ')
    → realize n b p1 p2 ρ'
(mkrel f1 f2) ∙ f = mkrel (λ x → f (f1 x)) (λ x → f (f2 x))

_T∙_ : {n : ℕ} {ρ ρ' : Set} {b : sphereT n} → realizeT n b ρ → (ρ → ρ') → realizeT n b ρ'
_T∙_ {zero} r f = ⋆
_T∙_ {succ n} r f = r ∙ f

{---- Stage 3: linked paths -----------------}

data linked-rel (n : ℕ) (b : sphereT n) (p1 p2 : path n b)  (ρ : Set) : (r : realize n b p1 p2 ρ) → Set where
 linked-rel/ : (f1 : p1 .t → ρ) (f2 : p2 . t → ρ) →
         (p1 .f T∙ f1) ≡ (p2 .f T∙ f2) → linked-rel n b p1 p2 ρ (mkrel f1 f2)

data linked-relT (ρ : Set) : (n : ℕ) (b : sphereT n) (r : realizeT n b ρ) → Set₁ where
 linked-relT/z : linked-relT ρ zero ⋆ ⋆
 linked-relT/s : {n : ℕ} {b : sphereT n} {p1 p2 : path n b} {r : realize n b p1 p2 ρ} →
    linked-rel n b p1 p2 ρ r →
    linked-relT ρ (succ n) (b , (p1 , p2)) r
