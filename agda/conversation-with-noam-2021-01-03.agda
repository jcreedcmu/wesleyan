module conversation-with-noam-2021-01-03 where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-

A species is a presheaf over the category of finite sets and
bijections.

Composition of species is given by

(F ∘ G)[a] = sum_{π part of A} F[π] × prod_{B ∈ π} G[B]

a symmetric operad is a monoid object for the monoidal
product ∘

given a species, build the free operad over that species

example: the terminal species, which has one permutation-invariant
structure for each size.

To give an operad, must give
- F a species and
- η: I → F
- μ: F ∘ F → F

the operad of trees is the free operad on the species 1
- F[α] : species of trees with inputs α
- μ : tree composition
- η : tree with one input

for any species S you can give an explicit formula
for the free operad on S, 𝓕S.

I is the species that is the "indicator of n=1"

       ⎧ {*} if n = 1
I[n] = ⎨
       ⎩ {} otherwise.

𝓕S = I + S ∘ 𝓕S

UMP for the free operad 𝓕S over S is:
given any other operad 𝒪 over S
α : S → 𝒪
there exists a unique operad morphism
𝓕 S ---→ 𝒪
such that
𝓕 S ---→ 𝒪
   ^      ↑
    \---- S

𝓕 is the left adjoint to the forgetful functor from operads to
species, which drops the monoid structure.

S → 𝓕 S is initial algebra for functor
G ↦ I + S ∘ G
-}

postulate
  plus : ℕ → ℕ → ℕ

mutual
 data PlanarTree (S : ℕ → Set) : (n : ℕ) → Set where
   leaf : PlanarTree S (succ zero)
   node : {n k : ℕ} → S k → Forest S k n
     → PlanarTree S n

 data Forest (S : ℕ → Set) : (k : ℕ) (n : ℕ) → Set where
   nil : Forest S zero zero
   cons : {m k n : ℕ} → PlanarTree S m → Forest S k n →
     Forest S (succ k) (plus n m)
