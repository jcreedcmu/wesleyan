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

data Unit {a} : Set a where
   ⋆ : Unit


data Rep : Set1 where
  rUnit : Rep
  rOther : Set → Rep

elm : Rep → Set
elm rUnit = Unit
elm (rOther A) = A

rΣ : (ρ : Rep) → (elm ρ → Set) → Set
rΣ rUnit B = (B ⋆)
rΣ (rOther A) B = Σ A B

module Tree1Simple where
 mutual
  Forest : Set → Set1
  Forest A = (a : A) → Tree

  data Tree : Set1 where
   var : Tree
   node : {A : Set} → Forest A → Tree


module Tree1 where
 record Siz {a} {b} : Set (lsuc a ⊔ lsuc b) where
   constructor siz
   field
     carrier : Set a
     span : carrier → Set b

 open Siz
 mutual
  data Forest {a} {b} (S : Siz {a} {b}) (c : S .carrier) : Set (b ⊔ lsuc lzero) where
   forest : (S .span c → Tree S) → Forest S c

  data Tree {a} {b} (S : Siz {a} {b}) : Set (b ⊔ lsuc lzero) where
   var : Tree S
   node : (c : S .carrier) → Forest S c → Tree S

 spanOfTree : ∀ {a b} (S : Siz {a} {b}) → Tree {a} {b} S → Set b
 spanOfTree S var = Unit
 spanOfTree S (node c x) = {!!}




-- mutual
--   {- the two arguments to Tree2 are the set of 1-d inputs, and the tree of 2-d inputs.
--   the 2-d output is uniquely given as the single-node tree with 1-d domain A  -}
--   data Tree2 : {A : Set} (T : Tree1 A) → Set1 where
--     var2 : {A : Set} → Tree2 (one-node A)
