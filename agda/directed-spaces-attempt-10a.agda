module directed-spaces-attempt-10a where

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


module Tree1Mod where
 record Siz {a} {b} : Set (lsuc a ⊔ lsuc b) where
   constructor siz
   field
     carrier : Set a
     span : carrier → Set b

 open Siz
 mutual
  data Forest {a} {b} (S : Siz {a} {b}) (c : S .carrier) : Set (lsuc b ⊔ a) where
   forest : (S .span c → Tree {a} {b} S) → Forest {a} {b} S c

  data Tree {a} {b} (S : Siz {a} {b}) : Set (lsuc b ⊔ a) where
   var : Tree {a} {b} S
   node : (c : S .carrier) → Forest {a} {b} S c → Tree {a} {b} S

 spanOfTree : ∀ {a b} (S : Siz {a} {b}) → Tree {a} {b} S → Set b
 spanOfTree {a} {b} S var = Unit
 spanOfTree {a} {b} S (node c (forest branches)) = Σ (S .span c) (λ elt → spanOfTree S (branches elt))

 treeSiz : ∀ {a} (n : ℕ) → Siz {lsuc a} {a}
 treeSiz {a} zero = siz (Set a) (λ x → x)
 treeSiz {a} (succ n) = siz (Tree (treeSiz n)) (λ t → spanOfTree (treeSiz n) t)


module Other where
 mutual
  data Tree : (n : ℕ) → Set1 where
   var : {n : ℕ} → Tree n
   node : {n : ℕ} (branches : Tree n) → (size branches → Tree (succ n)) → Tree (succ n)

  size : ∀ {n : ℕ} → Tree n → Set
  size var = Unit
  size (node t f) = Σ (size t) (λ b → size (f b))


module OtherInt where
  data Tree : (n : ℕ) (size : Set) → Set1 where
   var : {n : ℕ} → Tree n Unit
   node : {n : ℕ} {B : Set} {S : B → Set}
             → Tree n B
             → ((b : B) → Tree (succ n) (S b))
             → Tree (succ n) (Σ B S)

-- This I think is an actual correct representation of the trees I have in mind
module BetterInt where
  data Tree : (n : ℕ) (size : Set) → Set1 where
    set : (s : Set) → Tree zero s
    var : {n : ℕ} → Tree (succ n) Unit
    node : {n : ℕ} {B : Set} {S : B → Set}
              → Tree n B
              → ((b : B) → Tree (succ n) (S b))
              → Tree (succ n) (Σ B S)

  basic-tree : (S : Set) → Tree (succ zero) (Σ S (λ _ → Unit))
  basic-tree B = node {zero} {B = B} {S = λ _ → Unit} (set B) (λ b → var)

-- This is the same thing just expanded out
module BetterIntInline where
  data Tree1 : Set → Set1 where
    var1 : Tree1 Unit
    node1 : {B : Set} {S : B → Set}
              --
              → ((b : B) → Tree1 (S b))
              → Tree1 (Σ B S)


  data Tree2 : Set → Set1 where
    var2 : Tree2 Unit
    node2 : {B : Set} {S : B → Set}
              → Tree1 B
              → ((b : B) → Tree2 (S b))
              → Tree2 (Σ B S)


  data Tree3 : Set → Set1 where
    var3 : Tree3 Unit
    node3 : {B : Set} {S : B → Set}
              → Tree2 B
              → ((b : B) → Tree3 (S b))
              → Tree3 (Σ B S)

-- This is accomplishing the same thing by iterating an endomap on the
-- kind (Set → Set1)
module IntRec where
  data Bnch (Pr : Set → Set1) : Set → Set1 where
    var : Bnch Pr Unit
    node : {B : Set} {S : B → Set}
      → Pr B
      → ((b : B) → Bnch Pr (S b))
      → Bnch Pr (Σ B S)

  Tree : ℕ → Set → Set1
  Tree zero _ = Unit
  Tree (succ n) = Bnch (Tree n)

-- this is an attempt to accomplish the same sort of thing,
-- but by indexing on *the kind of data* that belongs at the leaves,
-- rather than indexing the leaf-sets themselves
module LabelledLeaves where
  data Tr {a b} (A : Set a) : (n : ℕ) → Set (a ⊔ lsuc b) where
    obj :  (B : Set) → (B → A) → Tr A zero
    lf :  {n : ℕ} → A → Tr A (succ n)
    nd : {n : ℕ}
              → Tr {b = b} (Tr {b = b} A (succ n)) n
              → Tr A (succ n)

-- By Grothendieck construction this would be essentially the same,
-- but agda can't tell it's terminating.
-- module LabelledLeaves2 where
--   data Tr (A : Set1) : (n : ℕ) → Set1 where
--     obj :  (A → Set) → Tr A zero
--     lf :  {n : ℕ} → A → Tr A (succ n)
--     nd : {n : ℕ}
--               → Tr (Tr A (succ n)) n
--               → Tr A (succ n)
