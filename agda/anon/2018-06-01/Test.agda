{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import 2018-06-01.Basics
open import 2018-06-01.Rewrites
open import 2018-06-01.Terms

module 2018-06-01.Test where

{-

I'm going to try guessing/constructing

Δ ; Γ, x - A  ⊢ A* : type
Δ ; Γ, x - A  ⊢ M : A*

for increasingly complicated A.

-}

{-

First, we have Δ ; x - A ⊢ A : type, when A is Γ-closed.

We don't syntactically dualize the Δ-variables appearing in A when
it appears on the left. We just understand the minus sign itself as
dualizing their appearances.

So the term we want to construct is

-}

MA : ((c : Obj1) → oA (c , c)) → tA
MA a = a

-- endA : (d e : Obj1) (f : Mor1 d e) → eA f MA
