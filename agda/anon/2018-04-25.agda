{-# OPTIONS --without-K --rewriting #-}

module 2018-04-25 where

open import HoTT hiding ( J )

-- module Foo (I : Set) (J : Set) (h : J → I) (A : I → Set) where

postulate
  I J : Set
  h : J → I
  A : I → Set

record Rel1 : Set₁ where
  field
    C : Set
    f : (i : I) → C → A i

record Rel2 : Set₁ where
  field
    D : Set
    g : (j : J) → D → A (h j)

push : Rel1 → Rel2
push R = record { D = C ; g = λ j c → f (h j) c } where
  open Rel1 R

record PullRec (R : Rel2) : Set where
  open Rel2 R
  field
    a : (i : I) → A i
    d : D
    p : (j : J) → g j d == a (h j)

pull : Rel2 → Rel1
pull R = record { C = PullRec R ; f = λ i ρ → ρ .PullRec.a i } where
  open Rel2 R

record Rel1Mor (ρ1 ρ2 : Rel1) : Set where
  open Rel1
  field
    Cp : ρ1 .C → ρ2 .C
    fp : (i : I) (c : ρ1 .C) → ρ2 .f i (Cp c) == ρ1 .f i c

record Rel2Mor (ρ1 ρ2 : Rel2) : Set where
  open Rel2
  field
    Dp : ρ1 .D → ρ2 .D
    gp : (j : J) (d : ρ1 .D) → ρ2 .g j (Dp d) == ρ1 .g j d

adjoint : (ρ1 : Rel1) (ρ2 : Rel2) → Rel2Mor (push ρ1) ρ2 == Rel1Mor ρ1 (pull ρ2)
adjoint ρ1 ρ2  = ua (equiv into out zig zag) where
  into : Rel2Mor (push ρ1) ρ2 → Rel1Mor ρ1 (pull ρ2)
  into μ = record {
       Cp = λ c → record {
         a = λ i → f i c ;
         d = Dp c ;
         p = λ j → gp j c } ;
       fp = λ i c → idp } where
    open Rel2Mor μ
    open Rel1 ρ1

  out : Rel1Mor ρ1 (pull ρ2) → Rel2Mor (push ρ1) ρ2
  out μ = record {
      Dp = λ d → Cp d .PullRec.d ;
      gp = λ j d → Cp d .PullRec.p j ∙ fp (h j) d } where
    open Rel1Mor μ

  zig : (b : Rel1Mor ρ1 (pull ρ2)) → into (out b) == b
  zig μ = {!!}
    where open Rel1Mor μ

  zag : (a : Rel2Mor (push ρ1) ρ2) → out (into a) == a
  zag μ = {!!}
    where open Rel2Mor μ
