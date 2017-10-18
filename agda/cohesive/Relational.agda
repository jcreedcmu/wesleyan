{-# OPTIONS --without-K #-}
module Relational where

open import HoTT hiding (_≤_ ; S)

idn : ∀ {i} {A : Type i} → (A → A)
idn {A} x = x

cpf : {A1 A2 B : Set} (f1 : A1 → B) (f2 : A2 → B) → (A1 ⊔ A2 → B)
cpf f1 f2 (inl x) = f1 x
cpf f1 f2 (inr x) = f2 x

zef : (B : Set) → (⊥ → B)
zef B ()

zpf-aeq : {X : Set} (f g : ⊥ → X) → f == g
zpf-aeq f g = λ= (λ ())

cpf-eq0 :  {A1 A2 B X : Set}  {c1 : A1 → X} {c2 : A2 → X} (d : X → B)
  (z : A1 ⊔ A2) → cpf (d ∘ c1) (d ∘ c2) z == d (cpf c1 c2 z)
cpf-eq0 d (inl x) = idp
cpf-eq0 d (inr x) = idp

cpf-eq : {A1 A2 B X : Set}  {c1 : A1 → X} {c2 : A2 → X} (d : X → B)
  → cpf (d ∘ c1) (d ∘ c2) == d ∘ cpf c1 c2
cpf-eq {A1} {A2} {c1 = c1} {c2} d = λ= (cpf-eq0 d)

postulate
  -- The 'walking relation' over any set
  ♯ : Set → Set
  η : {A : Set} (a : A) → ♯ A
  ♯F : {A B : Set} (f : A → B) → (♯ A → ♯ B)
  η-nat : {A B : Set} {f : A → B} → ♯F f ∘ η == η ∘ f

  -- The intent is that:
  -- f : ♯ 2 → Set is literally the same thing as
  --   a binary relation on f(η(0)) and f(η(1))
  -- f : ♯ 2 → X is somehow an 'internal binary relation'
  --   on f(η(0)) and f(η(1))

  -- 2-cells
  _≤_ : {A B : Set} (R S : ♯ A → B) → Set

  ≤r : {A B : Set} (R : ♯ A → B)
    → (R ≤ R)
  ≤t : {A B : Set} {R S T : ♯ A → B}
    → (R ≤ S) → (S ≤ T) → (R ≤ T)

  -- 'univalence'
  ≤univ : {A B : Set} (R S : ♯ A → B)
    → (α : R ≤ S) (β β' : S ≤ R)
    → ≤t α β == ≤r R → ≤t β' α == ≤r S
    → (R == S)

  -- I'm cheating and collapsing equality of ≤ morphisms to
  -- make proofs below easier as a warmup
  deleteme : {A B : Set} {R S : ♯ A → B}
    (α α' : R ≤ S) → α == α'

≤=r : {A B : Set} {R S : ♯ A → B}
   → (R == S) → (R ≤ S)
≤=r idp = ≤r _

{- this is sort of meant as backwards compatibility for the previous
  way I set all this up, but is a meaningful concept of the 'fiber
  over f' -}
fib : {A B : Set} (f : A → B) → Set
fib {A} {B} f = Σ (♯ A → B) (λ R → R ∘ η == f)

_≤f_ : {A B : Set} {f : A → B} (R S : fib f) → Set
R ≤f S = R .fst ≤ S .fst

-- this isn't really true, since it depends on deleteme
≤anti : {A B : Set} (R S : ♯ A → B)
  → (R ≤ S) → (S ≤ R) → (R == S)
≤anti R S α β = ≤univ R S α β β (deleteme (≤t α β) (≤r R)) (deleteme (≤t β α) (≤r S))

module _ {A B X : Set} {f : A → X} (g : B → A) where
  -- opreindexing
  push : fib f → fib (f ∘ g)
  push R = (R .fst) ∘ ♯F g  , ap (R .fst ∘_) (η-nat {f = g}) ∙ ap (_∘ g) (R .snd)

  postulate
    -- reindexing
    pull : fib (f ∘ g) → fib f

  pull1 : (R : ♯ B → X) (e : R ∘ η == f ∘ g) → ♯ A → X
  pull1 R e = pull (R , e) .fst

  pull= : (R : ♯ B → X) (e : R ∘ η == f ∘ g) → pull1 R e ∘ η == f
  pull= R e = pull (R , e) .snd

module _ {A B C X : Set} {f : A → X} (g : B → A) (h : C → B) where
  postulate
    push-act2 : (R : fib f) → push (g ∘ h) R == push h (push g R) -- should be provable
    pull-act2 : (T : fib (f ∘ g ∘ h)) → pull {f = f} (g ∘ h) T == pull g (pull h T)

module _ {A X : Set} {f : A → X} where
  postulate
    push-act0 : (R : fib f) → push idn R == R -- should be provable
    pull-act0 : (R : fib f) → pull idn R == R

postulate
  -- adjunction
  adj : {A B C : Set} {f : A → B} {g : C → A} (R : fib f) (S : fib (f ∘ g)) →
    (R ≤f pull g S) ≃ (push g R ≤f S)

  -- copairing
  copair : {A1 A2 B : Set} {f1 : A1 → B} {f2 : A2 → B}
    (R1 : fib f1) (R2 : fib f2) → fib (cpf f1 f2)
  -- this is the UMP of the product in a category living over (Sets/X)^op
  -- where heteromorphisms --- nonvertical morphisms in the total category ---
  -- are identified with (equivalently) both of
  -- R ≤f pull g S and push g R ≤f S
  copair= : {A1 A2 B X : Set}  {c1 : A1 → X} {c2 : A2 → X} (d : X → B)
    (R1 : fib (d ∘ c1)) (R2 : fib (d ∘ c2)) (S : fib d)
    → (S ≤f pull c1 R1) × (S ≤f pull c2 R2) ≃ (S ≤f pull (cpf c1 c2) (transport fib (cpf-eq d) (copair R1 R2)))

  -- zero
  zero : {B : Set} → fib (zef B)
  -- this is the UMP of the terminal object in a category living over (Sets/X)^op
  zero= : {B X : Set}  (d : X → B) (S : fib d)
    → is-contr (S ≤f pull (zef X) (transport fib (zpf-aeq (zef B) (d ∘ (zef X))) zero))

-- trivial element of fiber
triv : {A X : Set} (f : A → X) → fib f
triv {A} {X} f = pull (zef A) (transport fib (zpf-aeq (zef X) (f ∘ zef A)) zero)

zero=s : {B X : Set}  {d : X → B} (S : fib d) → S ≤f triv d
zero=s {d = d} S = zero= d S .fst

{-
One can start at *, and proceed to f ∘ b2 in two different ways;
we postulate that they're equal.

                pull
          f -----------> f ∘ b1
          |             *|
     push |              | push
          |              |
          v              v
        f ∘ b2 ------->  f ∘ b1 ∘ k1 = f ∘ b2 ∘ k2
                pull
-}

postulate
  beck-chevalley : {A B1 B2 K X : Set}
    {f : A → X}
    {b1 : B1 → A} {b2 : B2 → A}
    {k1 : K → B1} {k2 : K → B2}
    → (p : b1 ∘ k1 == b2 ∘ k2)
    → (R : fib (f ∘ b1))
    → push {f = f} b2 (pull {f = f} b1 R) ==
    pull {f = f ∘ b2} k2 (coe (ap (λ z → fib (f ∘ z)) p) (push {f = f ∘ b1} k1 R))

postulate
  -- copair-pres-push : {A B1 B2 X : Set} (f : A → X) (g1 : B1 → A) (g2 : B2 → A) (R : fib f)
  --   → push (cpf g1 g2) R == coe (ap fib (cpf-eq f)) (copair (push g1 R) (push g2 R))


  copair-pres-push : {A1 A2 B1 B2 X : Set}
    (f1 : A1 → X)  (f2 : A2 → X)
    (g1 : B1 → A1) (g2 : B2 → A2)
    (R1 : fib f1)  (R2 : fib f2)
    → push (cpf (inl ∘ g1) (inr ∘ g2)) (copair R1 R2) ==
      transport fib (cpf-eq (cpf f1 f2))
        (copair (push g1 R1) (push g2 R2))

--  transport (λ z → fib (z ∘ k1)) (cpf-eq (cpf g h)) (push k1 (copair R S))

push-transport :
  {A B X : Set}
  {f f' : A → X} (g : B → A) (R : fib f) (feq : f == f')
  → push g (transport fib feq R) ==
    transport (λ z → fib (z ∘ g)) feq (push g R)
push-transport g R idp = idp

transport-sub :
  {A B : Set} {b1 b2 : B} (P : A → Set) (q : B → A) (eq : b1 == b2) (thing : P (q b1))
  → (transport (P ∘ q) eq thing) == transport P (ap q eq) thing
transport-sub P q idp thing = idp

transport-lem : {A : Set} (P : A → Set) {a1 a2 a3 a4 : A} (thing : P a1)
  (e1 : a1 == a2) (e2 : a2 == a3) (e3 : a3 == a4) (e4 : a1 == a4) →
  e1 ∙ e2 ∙ e3 == e4 →
  transport P e4 thing == transport P e3 (transport P e2 (transport P e1 thing))
transport-lem P thing idp idp idp .idp idp = idp

postulate
  cp-eq-helper : {A B C : Set} (f1 f2 : A ⊔ B → C) (p q : f1 == f2)
    → ((a : A) → (ap (λ x → x (inl a)) p) == (ap (λ x → x (inl a)) q))
    → ((b : B) → (ap (λ x → x (inr b)) p) == (ap (λ x → x (inr b)) q))
    → p == q
-- cp-eq-helper f1 f2 p q ml mr = {!!}
