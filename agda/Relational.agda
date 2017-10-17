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

zpf-aeq : {X : Set} (f g : ⊥ → X) → f == g
zpf-aeq f g = λ= (λ ())


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
    → is-contr (S ≤ pull (zef X) (transport fib (zpf-aeq (zef B) (d ∘ (zef X))) zero))

zero=s : {B X : Set}  {d : X → B} (S : fib d) → S ≤ pull (zef X) (transport fib (zpf-aeq (zef B) (d ∘ zef X)) zero)
zero=s {d = d} S = zero= d S .fst

-- trivial element of fiber
triv : {A X : Set} (f : A → X) → fib f
triv {A} {X} f = pull (zef A) (transport fib (zpf-aeq (zef X) (f ∘ zef A)) zero)

sing : {X : Set} (x : X) → (⊤ → X)
sing x tt = x

module E1 where
  -- product of two relations over the same support
  join : {B X : Set} (f : B → X) (R S : fib f) → fib f
  join f R S = pull (cpf idn idn) (transport fib (cpf-eq f) (copair R S))

  -- joining with a trivial relation is the identity
  jointriv : {B X : Set} (f : B → X) (R : fib f) → R == join f R (triv f)
  jointriv f R = ≤anti R (join f R (triv f)) jointriv1 jointriv2 where
    jointriv1 : R ≤ join f R (triv f)
    jointriv1 = –> (copair= f R (triv f) R) (≤=r (! (pull-act0 R)) , ≤t (zero=s R) (≤=r (!(pull-act0 (triv f)))))

    jointriv2a : join f R (triv f) ≤ pull idn R
    jointriv2a = <– (copair= f R (triv f) (join f R (triv f))) (≤r (join f R (triv f))) .fst

    jointriv2 : join f R (triv f) ≤ R
    jointriv2 = ≤t jointriv2a (≤=r (pull-act0 R))


module E2 where
  pullf : {A B : Set} → (A ⊔ B) ⊔ B → (A ⊔ B)
  pullf = cpf idn inr

  cpf-lem : {A B X : Set} (f : A → X) (g : B → X) → cpf (cpf f g) g == cpf f g ∘ (cpf idn inr)
  cpf-lem {A} {B} f g = cpf-eq (cpf f g)

  -- join of two relations over overlapping support
  join : {A B X : Set} {f : A → X} {g : B → X} (R : fib (cpf f g)) (S : fib g) → fib (cpf f g)
  join {f = f} {g} R S = pull pullf (transport fib (cpf-lem f g) (copair R S))

  jointriv : {A B X : Set} (f : A → X) (g : B → X) (R : fib (cpf f g))
    → push inl R == triv f
    → push inl (join R (triv g)) == triv f
  jointriv {A} {B} {X} f g R p = ap (push inl) (! lem1) ∙ p where
    from1 : (R ≤ pull idn R) × (R ≤ pull inr (triv g)) → (R ≤ join R (triv g))
    from1 = –> (copair= {c1 = idn} {c2 = inr} (cpf f g) R (triv g) R)

    froma : R ≤ pull idn R
    froma = ≤=r (! (pull-act0 R))

    zeg : zef X == cpf f g ∘ inr ∘ zef B
    zeg = zpf-aeq (zef X) (g ∘ (zef B))

    zecpf : zef X == cpf f g ∘ zef (A ⊔ B)
    zecpf = zpf-aeq (zef X) (cpf f g ∘ zef (A ⊔ B))

    from2 : pull (inr ∘ zef B) (transport fib zeg zero) ≤ pull inr (triv g)
    from2 = ≤=r (pull-act2 inr (zef B) (transport fib zeg zero))

    lconcrete : {C X : Set} (d : C → X) (m q : ⊥ → C) →
      pull {f = d} m (transport fib (zpf-aeq (zef X) (d ∘ m)) zero) ==
      pull {f = d} q (transport fib (zpf-aeq (zef X) (d ∘ q)) zero)
    lconcrete {X = X} d m q = ap (λ t → pull t (transport fib (zpf-aeq (zef X) (d ∘ t)) zero)) (zpf-aeq m q)

    from3 :
      pull (zef (A ⊔ B)) (transport fib zecpf zero) ≤
      pull (inr ∘ zef B) (transport fib zeg zero)
    from3 = ≤=r (lconcrete (cpf f g) (zef (A ⊔ B)) (inr ∘ zef B))

    fromb : R ≤ pull inr (triv g)
    fromb =  ≤t (zero=s R) (≤t from3 from2)

    fromlem : R ≤ join R (triv g)
    fromlem = from1 (froma , fromb)

    to1 : join R (triv g) ≤ pull idn R
    to1 =  <– (copair= (cpf f g) R (triv g) (join R (triv g))) (≤r (join R (triv g))) .fst

    tolem : join R (triv g) ≤ R
    tolem = ≤t to1 (≤=r (pull-act0 R))

    lem1 : R == join R (triv g)
    lem1 = ≤anti R (join R (triv g)) fromlem tolem
