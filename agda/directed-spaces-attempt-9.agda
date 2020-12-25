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

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

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
  data Forest {a} {b} (S : Siz {a} {b}) (c : S .carrier) : Set (lsuc b ⊔ a) where
   forest : (S .span c → Tree {a} {b} S) → Forest {a} {b} S c

  data Tree {a} {b} (S : Siz {a} {b}) : Set (lsuc b ⊔ a) where
   var : Tree {a} {b} S
   node : (c : S .carrier) → Forest {a} {b} S c → Tree {a} {b} S

 spanOfTree : ∀ {a b} (S : Siz {a} {b}) → Tree {a} {b} S → Set b
 spanOfTree {a} {b} S var = Unit
 spanOfTree {a} {b} S (node c (forest branches)) = Σ (S .span c) (λ elt → spanOfTree S (branches elt))

 treeSiz : ∀ {a} (n : Nat) → Siz {lsuc a} {a}
 treeSiz {a} zero = siz (Set a) (λ x → x)
 treeSiz {a} (succ n) = siz (Tree (treeSiz n)) (λ t → spanOfTree (treeSiz n) t)


module Other where
 mutual
  data Tree : (n : Nat) → Set1 where
   var : {n : Nat} → Tree n
   node : {n : Nat} (branches : Tree n) → (size branches → Tree (succ n)) → Tree (succ n)

  size : ∀ {n : Nat} → Tree n → Set
  size var = Unit
  size (node t f) = Σ (size t) (λ b → size (f b))


module OtherInt where
  data Tree : (n : Nat) (size : Set) → Set1 where
   var : {n : Nat} → Tree n Unit
   node : {n : Nat} {B : Set} {S : B → Set}
             → Tree n B
             → ((b : B) → Tree (succ n) (S b))
             → Tree (succ n) (Σ B S)


 -- treeSiz0 : ∀ {a} → Siz {lsuc a} {a}
 -- treeSiz0 {a} = siz (Set a) (λ x → x)

 -- treeSiz1 : ∀ {a} → Siz {lsuc a} {a}
 -- treeSiz1 {a} = siz (Tree treeSiz0) (λ t → spanOfTree treeSiz0 t)

 -- treeSiz2 : ∀ {a} → Siz {lsuc a} {a}
 -- treeSiz2 {a} = siz (Tree treeSiz1) (λ t → spanOfTree treeSiz1 t)
