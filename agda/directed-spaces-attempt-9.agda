module directed-spaces-attempt-9 where

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


l3 : Level
l3 = lsuc (lsuc (lsuc (lzero)))

module Tree0 where
 record Siz {a} : Set (lsuc a) where
   constructor siz
   field
     carrier : Set a
     span : carrier → Set

 open Siz
 mutual
  data Forest {a}  (S : Siz {a} ) (c : S .carrier) : Set (lsuc lzero ⊔ a) where
   forest : (S .span c → Tree {a}  S) → Forest {a}  S c

  data Tree {a}  (S : Siz {a} ) : Set (lsuc lzero ⊔ a) where
   var : Tree {a}  S
   node : (c : S .carrier) → Forest {a}  S c → Tree {a}  S


-- module Tree1 where
--  record Siz {a} {b} : Set (lsuc a ⊔ lsuc b) where
--    constructor siz
--    field
--      carrier : Set a
--      span : carrier → Set b

--  open Siz
--  mutual
--   data Forest {a} {b} (S : Siz {a} {b}) (c : S .carrier) : Set (b ⊔ lsuc lzero) where
--    forest : (S .span c → Tree {a} {b} S) → Forest {a} {b} S c

--   data Tree {a} {b} (S : Siz {a} {b}) : Set (b ⊔ lsuc lzero) where
--    var : Tree {a} {b} S
--    node : (c : S .carrier) → Forest {a} {b} S c → Tree {a} {b} S

--  -- spanOfTree : ∀ {a b} (S : Siz {a} {b}) → Tree {a} {b} S → Set (b ⊔ lsuc lzero)
--  -- spanOfTree {a} {b} S var = Unit {lsuc lzero ⊔ b}
--  -- spanOfTree {a} {b} S (node c (forest branches)) = Σ {b} {lsuc lzero ⊔ b} (S .span c) (λ elt → spanOfTree S (branches elt))




-- mutual
--   {- the two arguments to Tree2 are the set of 1-d inputs, and the tree of 2-d inputs.
--   the 2-d output is uniquely given as the single-node tree with 1-d domain A  -}
--   data Tree2 : {A : Set} (T : Tree1 A) → Set1 where
--     var2 : {A : Set} → Tree2 (one-node A)
