module parametricity where

open import HoTT

record Ob : Set₁ where
  constructor ob
  field
    F : Set → Set
    FR : {X Y : Set} (R : X → Y → Set) → F X → F Y → Set

record Mor (A B : Ob) : Set₁ where
  constructor mor
  open Ob
  field
    α : (X : Set) → F A X → F B X
    .nat : {X Y : Set} (R : X → Y → Set) (x : F A X) (y : F A Y)
      → FR A R x y → FR B R (α _ x) (α _ y)

V : Ob
V = ob (λ x → x) (λ x → x)

idm : {X : Ob} → Mor X X
idm {X} = mor (λ _ x → x) (λ R x y z → z)


module _ where
  open Mor
  open Ob

  moreq : (A B : Ob) (M N : Mor A B) → (α M == α N) → M == N
  moreq A B (mor α₁ nat₁) (mor .α₁ nat₂) idp = idp

  lem : (m : Mor V V) → α m == idf
  lem m = λ= (λ Y → λ= (λ z → nat m (λ u w → w == z) tt z idp))

thm : (m : Mor V V) → m == idm {V}
thm m = moreq V V m idm (lem m)
