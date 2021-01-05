module directed-spaces-attempt-12 where

open import Agda.Primitive

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

data Unit {a} : Set a where
   ⋆ : Unit

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

module Basic where

  data Tr1 : Set1 where
    lf : Tr1
    nd : (B : Set) (bs : B → Tr1) → Tr1

  dom1 : Tr1 → Set
  dom1 lf = Unit
  dom1 (nd B bs) = Σ B (λ b → dom1 (bs b))

  cod1 : Tr1 → Set
  cod1 t = Unit

module Int where

  data compose : (B : Set) (Bs : B → Set) (cod : Set) → Set where
   c1 : {B : Set} {Bs : B → Set} → compose B Bs (Σ B Bs)
   c2 : {B : Set} → compose B (λ _ → Unit) B

  data Tr1 : (dom : Set) → Set1 where
    lf : Tr1 Unit
    nd : {B : Set} {Bs : B → Set} {cod : Set} (bs : (b : B) → Tr1 (Bs b)) → compose B Bs cod → Tr1 cod

  canonical : (dom : Set) → Tr1 dom
  canonical dom = nd (λ _ → lf) c2

  mutual
   -- a mapping from the nodes of the tree t to appropriately shaped Tr2's
   mapping2 : {B : Set} (t : Tr1 B) → Set
   mapping2 lf = {!!}
   mapping2 (nd bs x) = {!!}

   data Tr2 : (dom1 : Set) (dom2 cod2 : Tr1 dom1)→ Set2 where
     lf : (dom1 : Set) → Tr2 dom1 (canonical dom1) (canonical dom1)
     nd : (dom1 : Set) (dom2 : Tr1 dom1) → (t : Tr1 dom1) →
       (bs : mapping2 t) → Tr2 dom1 dom2 t
