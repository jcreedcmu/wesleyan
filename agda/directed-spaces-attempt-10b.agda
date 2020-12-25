module directed-spaces-attempt-10b where

open import Agda.Primitive

data Unit {a} : Set a where
   ⋆ : Unit

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

module Basic where
  data Tr (A : Set1) : (n : ℕ) → Set1 where
    obj : (B : Set) → (B → A) → Tr A zero
    lf : {n : ℕ} → A → Tr A (succ n)
    nd : {n : ℕ} → Tr (Tr A (succ n)) n → Tr A (succ n)

  basic-tree : (A : Set) → Tr Unit (succ zero)
  basic-tree A = nd (obj A (λ _ → lf ⋆))

  data Bool : Set where
    true : Bool
    false : Bool

  cond : ∀ {a} {A : Set a} → Bool → A → A → A
  cond true x y = x
  cond false x y = y

  data Void : Set where

  abort : ∀ {a} {A : Set a} → Void → A
  abort ()

  tree1 : Set1
  tree1 = Tr Unit (succ zero)

  leaf : tree1
  leaf = lf ⋆

  dot : tree1
  dot = nd (obj Void abort)

  bin-node : tree1 → tree1 → tree1
  bin-node t1 t2 = nd (obj Bool (λ x → cond x t1 t2))

  assoc-tree : Tr Unit (succ zero)
  assoc-tree = bin-node (bin-node leaf leaf) leaf

  Gt : Set2
  Gt = {A : Set1} → A → Tr A (succ zero)

  gleaf1 : Gt
  gleaf1 = lf

  gbin1 : Gt → Gt → Gt
  gbin1 t1 t2 a = nd (obj Bool (λ x → cond x (t1 a) (t2 a)))

  assoc-red-tree : Tr Unit (succ (succ zero))
  assoc-red-tree = nd ( gbin1 (gbin1 gleaf1 gleaf1) gleaf1 (lf ⋆))

  generalize-tree : Tr Unit (succ zero) → Gt
  generalize-tree (lf x) a = lf a
  generalize-tree (nd t) {A} a = nd (obj {!!} {!!})

-- This seems like it should be right, but agda can't tell that it's
-- terminating.

-- module Iter where
--   data Tr (Pr : Set → Set) (A : Set) : Set where
--     lf : A → Tr Pr A
--     nd : Pr (Tr Pr A) → Tr Pr A

module Refine where
 data Tr {a b c} (A : Set a) (U : Set b) (El : U → Set c) : (n : ℕ) → Set (a ⊔ b ⊔ c) where
    obj : (C : U) → (El C → A) → Tr A U El zero
    lf : {n : ℕ} → A → Tr A U El (succ n)
    nd : {n : ℕ} → Tr (Tr A U El (succ n)) U El n → Tr A U El (succ n)

 Tree : (A : Set) (n : ℕ) → Set1
 Tree A n = Tr A Set (λ x → x) n

 -- This breaks down bc of level errors :(

 -- map : ∀ {a b c} (A B : Set a) (U : Set b) (El : U → Set c) (n : ℕ)
 --   → (f : A → B) → Tr A U El n → Tr B U El n
 -- map A B U El zero f (obj u bs) = obj u (λ x → f (bs x))
 -- map A B U El (succ n) f (lf x) = lf (f x)
 -- map A B U El (succ n) f (nd t) = nd {!map A B U El n f t!}
