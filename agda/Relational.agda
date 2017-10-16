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

zpf-eq : {A X : Set} (f : A → X) → zef X == f ∘ (zef A)
zpf-eq f = λ= (λ ())

cpf-eq : {A1 A2 B X : Set}  {c1 : A1 → X} {c2 : A2 → X} (d : X → B)
  → cpf (d ∘ c1) (d ∘ c2) == d ∘ cpf c1 c2
cpf-eq {A1} {A2} {c1 = c1} {c2} d = λ= cpf-eq0 where
  cpf-eq0 : (z : A1 ⊔ A2) → cpf (d ∘ c1) (d ∘ c2) z == d (cpf c1 c2 z)
  cpf-eq0 (inl x) = idp
  cpf-eq0 (inr x) = idp

postulate
  -- fiber over every function
  fib : {A B : Set} → (A → B) → Set
  -- hom
  _≤_ : {A B : Set} {f : A → B} (R S : fib f) → Set

  ≤r : {A B : Set} {f : A → B} (R : fib f)
    → (R ≤ R)
  ≤t : {A B : Set} {f : A → B} {R S T : fib f}
    → (R ≤ S) → (S ≤ T) → (R ≤ T)

  -- 'univalence'
  ≤univ : {A B : Set} {f : A → B} (R S : fib f)
    → (α : R ≤ S) (β β' : S ≤ R)
    → ≤t α β == ≤r R → ≤t β' α == ≤r S
    → (R == S)

  -- I'm cheating and collapsing equality of ≤ morphisms to
  -- make proofs below easier as a warmup
  deleteme : {A B : Set} {f : A → B} {R S : fib f}
    (α α' : R ≤ S) → α == α'

≤=r : {A B : Set} {f : A → B} {R S : fib f}
   → (R == S) → (R ≤ S)
≤=r idp = ≤r _

-- this isn't really true, since it depends on deleteme
≤anti : {A B : Set} {f : A → B} (R S : fib f)
  → (R ≤ S) → (S ≤ R) → (R == S)
≤anti R S α β = ≤univ R S α β β (deleteme (≤t α β) (≤r R)) (deleteme (≤t β α) (≤r S))

module _ {A B X : Set} {f : A → X} (g : B → A) where
  postulate
    -- opreindexing
    push : (R : fib f) → fib (f ∘ g)
    -- reindexing
    pull : (S : fib (f ∘ g)) → fib f

module _ {A B C X : Set} {f : A → X} (g : B → A) (h : C → B) where
  postulate
    push-act2 : (R : fib f) → push (g ∘ h) R == push h (push g R)
    pull-act2 : (T : fib (f ∘ g ∘ h)) → pull {f = f} (g ∘ h) T == pull g (pull h T)

module _ {A X : Set} {f : A → X} where
  postulate
    push-act0 : (R : fib f) → push idn R == R
    pull-act0 : (R : fib f) → pull idn R == R

postulate
  -- adjunction
  adj : {A B C : Set} {f : A → B} {g : C → A} (R : fib f) (S : fib (f ∘ g)) →
    (R ≤ pull g S) ≃ (push g R ≤ S)

  -- copairing
  copair : {A1 A2 B : Set} {f1 : A1 → B} {f2 : A2 → B}
    (R1 : fib f1) (R2 : fib f2) → fib (cpf f1 f2)
  -- this is the UMP of the product in a category living over (Sets/X)^op
  -- where heteromorphisms --- nonvertical morphisms in the total category ---
  -- are identified with (equivalently) both of
  -- R ≤ pull g S and push g R ≤ S
  copair= : {A1 A2 B X : Set}  {c1 : A1 → X} {c2 : A2 → X} (d : X → B)
    (R1 : fib (d ∘ c1)) (R2 : fib (d ∘ c2)) (S : fib d)
    → (S ≤ pull c1 R1) × (S ≤ pull c2 R2) ≃ (S ≤ pull (cpf c1 c2) (transport fib (cpf-eq d) (copair R1 R2)))

  -- zero
  zero : {B : Set} → fib (zef B)
  -- this is the UMP of the terminal object in a category living over (Sets/X)^op
  zero= : {B X : Set}  (d : X → B) (S : fib d)
    → is-contr (S ≤ pull (zef X) (transport fib (zpf-eq d) zero))

zero=s : {B X : Set}  {d : X → B} (S : fib d) → S ≤ pull (zef X) (transport fib (zpf-eq d) zero)
zero=s {d = d} S = zero= d S .fst

-- trivial element of fiber
triv : {A X : Set} (f : A → X) → fib f
triv {A} {X} f = pull (zef A) (transport fib (zpf-eq f) zero)

sing : {X : Set} (x : X) → (⊤ → X)
sing x tt = x

-- product of two relations over the same support
join : {A X : Set} (f : A → X) (R S : fib f) → fib f
join f R S = pull (cpf idn idn) (transport fib (cpf-eq f) (copair R S))

-- joining with a trivial relation is the identity
jointriv : {A X : Set} (f : A → X) (R : fib f) → R == join f R (triv f)
jointriv f R = ≤anti R (join f R (triv f)) jointriv1 jointriv2 where
  jointriv1 : R ≤ join f R (triv f)
  jointriv1 = –> (copair= f R (triv f) R) (≤=r (! (pull-act0 R)) , ≤t (zero=s R) (≤=r (!(pull-act0 (triv f)))))

  jointriv2a : join f R (triv f) ≤ pull idn R
  jointriv2a = <– (copair= f R (triv f) (join f R (triv f))) (≤r (join f R (triv f))) .fst

  jointriv2 : join f R (triv f) ≤ R
  jointriv2 = ≤t jointriv2a (≤=r (pull-act0 R))
