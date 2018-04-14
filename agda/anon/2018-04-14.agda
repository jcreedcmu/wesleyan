{-# OPTIONS --without-K --rewriting #-}

module 2018-04-14 where

open import HoTT hiding ( O ; Span )

copair : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
         (f : A → C) (g : B → C) → (A ⊔ B) → C
copair f g (inl x) = f x
copair f g (inr x) = g x

abort : ∀ {n} (C : Set n) → ⊥ → C
abort C ()

abortLem : ∀ {ℓ} {A : Set ℓ} {a : A} (nope : ⊥) → abort A nope == a
abortLem ()

takeFst : Unit → Bool
takeFst tt = false

module Idea3 where

 postulate
   R : ∀ {ℓ ℓ'} {A : Set ℓ'} {B : Set ℓ} → (A → B) → Set (lmax ℓ ℓ')
   push : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
     (f : A → B) {g : B → C} → R g → R (g ∘ f)
   coprod : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
     {f : A → C} {g : B → C} → R f → R g → R (copair f g)
   empty : ∀ {ℓ} {C : Set ℓ} → R (abort C)

   coprod' : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
     {f : A ⊔ B → C} → R (λ x → f (inl x)) → R (λ x → f (inr x)) → R f
   empty' : ∀ {ℓ} {C : Set ℓ} (f : ⊥ → C) → R f

   pull : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
     (f : A → B) (g : B → C) → R (g ∘ f) → R g
   -- somehow express that push ⊣ pull?
   rua : ∀ {ℓ ℓ'} {N : Set ℓ'} {C : Set ℓ} (A : N → Set ℓ)
     → R A == Σ (Set ℓ) (λ C → (n : N) → C → A n )

 Bridge : ∀ {ℓ} {A : Set ℓ} (a a' : A) → Set ℓ
 Bridge a a' = R (λ x → if x then a' else a)

 UnitBridge : ∀ {ℓ} {A : Set ℓ} (a : A) → Set ℓ
 UnitBridge a = R (λ { tt → a })

 TrivUnitBridge : ∀ {ℓ} {A : Set ℓ} (a : A) → UnitBridge a
 TrivUnitBridge a = pull _ _ (empty' _)

 isFunctional : ∀ {ℓ} {A : Set ℓ} {a a' : A} → Bridge a a' → Set ℓ
 isFunctional {A = A} {a} {a'} β = push takeFst β == TrivUnitBridge a

 data Tern : Set where
   t1 t2 t3 : Tern

 -- Bah, I don't seem to actually avoid the annoying case-by-case equality proofs
 -- even when I use coprod'

 -- compose' : ∀ {ℓ} {A : Set ℓ} {a b c : A} → Bridge a b → Bridge b c → Bridge a c
 -- compose' {A = A} {a} {b} {c} f g = {!!} where
 --   fourToThree : Bool ⊔ Bool → Tern
 --   fourToThree z = Coprod-elim (λ x → if x then t2 else t1) (λ x → if x then t3 else t2) z

 --   threeToA : Tern → A
 --   threeToA t1 = a
 --   threeToA t2 = b
 --   threeToA t3 = c

 --   interm : R threeToA
 --   interm = pull fourToThree threeToA (coprod' {f = λ w → threeToA (fourToThree w)} {!f!} {!!})

 compose : ∀ {ℓ} {A : Set ℓ} {a b c : A} → Bridge a b → Bridge b c → Bridge a c
 compose {A = A} {a} {b} {c} f g = transport R (λ= p') (push twoToThree interm) where
   fourToThree : Bool ⊔ Bool → Tern
   fourToThree (inl false) = t1
   fourToThree (inl true) = t2
   fourToThree (inr false) = t2
   fourToThree (inr true) = t3

   threeToA : Tern → A
   threeToA t1 = a
   threeToA t2 = b
   threeToA t3 = c

   p : (bb : Bool ⊔ Bool) →
     copair (λ x → if x then b else a) (λ x → if x then c else b) bb ==
     threeToA (fourToThree bb)
   p (inl false) = idp
   p (inl true) = idp
   p (inr false) = idp
   p (inr true) = idp

   twoToThree : Bool → Tern
   twoToThree false = t1
   twoToThree true = t3

   interm : R threeToA
   interm = pull fourToThree threeToA (transport R (λ= p) (coprod f g))

   p' : (bb : Bool) →
     threeToA (twoToThree bb) == (if bb then c else a)
   p' false = idp
   p' true = idp


-- 2 + 2 → A
-- 2 + 2 → 3 → A
module Idea2 where
 _✯_ : ∀ {n} → Set n → Set n → Set n
 A ✯ B = Σ (A → B) Idea3.R
 -- intent: A ✯ B = ♯ A → B

 η : ∀ {n} {B C : Set n} → B ✯ C → (B → C)
 η (f , _) = f

 push : {A B C : Set} → (A → B) → (B ✯ C) → (A ✯ C)
 push f (g , r) = (g ∘ f) , (Idea3.push f r)

 coprod : ∀ {n} {A B C : Set n} → (A ✯ C) → (B ✯ C) → (A ⊔ B) ✯ C
 coprod (f1 , r1) (f2 , r2) = (copair f1 f2 , Idea3.coprod r1 r2)

 pull : ∀ {n} {A B C : Set n} (f : A → B) (g : B → C) (h : A ✯ C)
   → (η h == g ∘ f) → B ✯ C
 pull f g (h , r) s = (g , Idea3.pull f g (transport Idea3.R s r))

module Idea where
 postulate
   ♯ : ∀ {n} → Set n → Set n
   η : ∀ {n} {A : Set n} → A → ♯ A
   push : {A B : Set} → (A → B) → ♯ A → ♯ B
   pull : ∀ {n} {A B C : Set n} (f : A → B) (g : ♯ A → C) (h : B → C)
     → ((a : A) → g (η a) == h (f a)) → ♯ B → C
   coprod : ∀ {n} {A B : Set n} → ♯ (A ⊔ B) → ♯ A ⊔ ♯ B

 record Span (N : Set) : Set₁ where
   field
     ℂ : Set
     𝔸 : N → Set
     𝕗 : (n : N) → ℂ → 𝔸 n
 open Span

 setPull : {A B : Set} (f : A → B) (g : Span A) (h : B → Set)
     → ((a : A) → g .𝔸 a == h (f a)) → Span B
 setPull {A} {B} f g h p = record {
   ℂ = Σ ((b : B) → h b) (λ ρ' → Σ (g .ℂ) (λ ρ →
        (a : A) → coe (p a) (g .𝕗 a ρ) == ρ' (f a) )) ;
   𝔸 = h ;
   𝕗 = λ x y → y .fst x }
