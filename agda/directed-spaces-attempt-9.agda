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


data Rep : Set where
  rUnit : Rep

elm : Rep → Set
elm rUnit = Unit

rΣ : ∀ {a} (ρ : Rep) → (elm ρ → Set a) → Set a
rΣ rUnit body = (body ⋆)

-- module Tree1Intrinsic where
--   data Tree : Set → Set1 where
--      var : Tree Unit
--      node : {A : Set} {B : A → Set} → ((a : A) → Tree (B a)) → Tree (Σ A B)

mutual
  {- Forest T S A
  is some structure whose inputs look like S, and whose outputs look like A. We
  carve up inputs S into chunks, and pass each one to T to tell us what kind of
  node goes there. -}
  data Forest1 (T : Set → Set1) : Set → Set → Set1 where
    forest1 : {A : Set} {B : A → Set} → ((a : A) → T (B a)) → Forest1 T (Σ A B) A

  data Tree1 : Set → Set1 where
    var1 : Tree1 Unit
    node1 : {A S : Set} → Forest1 Tree1 S A → Tree1 S


just : Set → Set
just A = Σ Unit (λ _ → A)

one-node : (A : Set) → Tree1 (just A)
one-node A = node1 {Unit} {just A} (forest1  (λ _ → node1 {!forest1 ?!}))

mutual
  {- the two arguments to Tree2 are the set of 1-d inputs, and the tree of 2-d inputs.
  the 2-d output is uniquely given as the single-node tree with 1-d domain A  -}
  data Tree2 : {A : Set} (T : Tree1 A) → Set1 where
    var2 : {A : Set} → Tree2 (one-node A)
