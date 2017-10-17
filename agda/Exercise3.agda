{-# OPTIONS --without-K #-}
module Exercise3 where

open import HoTT hiding (_≤_ ; S)
open import Relational

pullf : {B C : Set} → B ⊔ (B ⊔ C) → (B ⊔ C)
pullf = cpf inl idn

cpf-lem : {B C X : Set} (g : B → X) (h : C → X) → cpf g (cpf g h) == cpf g h ∘ (cpf inl idn)
cpf-lem {B} {C} g h = cpf-eq (cpf g h)

-- join of two relations over overlapping support
join : {B C X : Set} {g : B → X} {h : C → X} (R : fib g) (S : fib (cpf g h)) → fib (cpf g h)
join {g = g} {h} R S = pull pullf (transport fib (cpf-lem g h) (copair R S))

jointriv : {B C X : Set} (g : B → X) (h : C → X) (R : fib g) (S : fib (cpf g h))
  → push inl S == triv g
  → push inl (join R S) == R
jointriv {A} {B} {X} f g R p = {!!}
--   from1 : (R ≤ pull idn R) × (R ≤ pull inr (triv g)) → (R ≤ join R (triv g))
--   from1 = –> (copair= {c1 = idn} {c2 = inr} (cpf f g) R (triv g) R)

--   froma : R ≤ pull idn R
--   froma = ≤=r (! (pull-act0 R))

--   zeg : zef X == cpf f g ∘ inr ∘ zef B
--   zeg = zpf-aeq (zef X) (g ∘ (zef B))

--   zecpf : zef X == cpf f g ∘ zef (A ⊔ B)
--   zecpf = zpf-aeq (zef X) (cpf f g ∘ zef (A ⊔ B))

--   from2 : pull (inr ∘ zef B) (transport fib zeg zero) ≤ pull inr (triv g)
--   from2 = ≤=r (pull-act2 inr (zef B) (transport fib zeg zero))

--   lconcrete : {C X : Set} (d : C → X) (m q : ⊥ → C) →
--     pull {f = d} m (transport fib (zpf-aeq (zef X) (d ∘ m)) zero) ==
--     pull {f = d} q (transport fib (zpf-aeq (zef X) (d ∘ q)) zero)
--   lconcrete {X = X} d m q = ap (λ t → pull t (transport fib (zpf-aeq (zef X) (d ∘ t)) zero)) (zpf-aeq m q)

--   from3 :
--     pull (zef (A ⊔ B)) (transport fib zecpf zero) ≤
--     pull (inr ∘ zef B) (transport fib zeg zero)
--   from3 = ≤=r (lconcrete (cpf f g) (zef (A ⊔ B)) (inr ∘ zef B))

--   fromb : R ≤ pull inr (triv g)
--   fromb =  ≤t (zero=s R) (≤t from3 from2)

--   fromlem : R ≤ join R (triv g)
--   fromlem = from1 (froma , fromb)

--   to1 : join R (triv g) ≤ pull idn R
--   to1 =  <– (copair= (cpf f g) R (triv g) (join R (triv g))) (≤r (join R (triv g))) .fst

--   tolem : join R (triv g) ≤ R
--   tolem = ≤t to1 (≤=r (pull-act0 R))

--   lem1 : R == join R (triv g)
--   lem1 = ≤anti R (join R (triv g)) fromlem tolem
