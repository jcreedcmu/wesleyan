module directed-spaces-attempt-9 where

open import Agda.Primitive


record Σ {a b} (A : Set a) (B : A → Set a) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

data Unit : Set where
   ⋆ : Unit


module Tree1 where
  data Tree : Set1 where
     var : Tree
     node : {A : Set} → (A → Tree) → Tree

  mutual
    domain_t : Tree → Set
    domain_t var = Unit
    domain_t (node forest) = domain_f forest

    domain_f : {X : Set} → (X → Tree) → Set
    domain_f {X} forest = Σ[ x ∈ X ] domain_t (forest x)

module Tree1Intrinsic where
  data Tree : Set → Set1 where
     var : Tree Unit
     node : {A : Set} {B : A → Set} → ((a : A) → Tree (B a)) → Tree (Σ A B)


module Tree2Intrinsic (Tree : Set → Set1) where

  ComposableForest : {A : Set} (t : Tree A) → Set1
  ComposableForest = {!!}

  compose : {A : Set} (t : Tree A) → ComposableForest t → Tree A
  compose = {!!}

  data Tree2 : {A : Set} → Tree A → Set1 where
     var : {A : Set} (t : Tree A) → Tree2 t
     node : {A : Set} (t : Tree A) (B : ComposableForest t)
       -- replacement of every node A in t with a Tree2
       → Tree2 (compose t B)
