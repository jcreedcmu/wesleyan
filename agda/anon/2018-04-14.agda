{-# OPTIONS --without-K --rewriting #-}

module 2018-04-14 where

open import HoTT hiding ( O ; Span )

copair : ∀ {n} {A B C : Set n} (f : A → C) (g : B → C) → (A ⊔ B) → C
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
   coprod : ∀ {ℓ} {A B C : Set ℓ} {f : A → C} {g : B → C} → R f → R g → R (copair f g)
   empty : ∀ {ℓ} {C : Set ℓ} → R (abort C)
   pull : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
     (f : A → B) (g : B → C) → R (g ∘ f) → R g
   -- somehow express that push ⊣ pull?
   rua : ∀ {ℓ ℓ'} {N : Set ℓ'} {C : Set ℓ} (A : N → Set ℓ)
     → R A == Σ (Set ℓ) (λ C → (n : N) → C → A n )

 Bridge : ∀ {ℓ} {A : Set ℓ} (a a' : A) → Set ℓ
 Bridge a a' = R (λ x → if x then a' else a)

 UnitBridge : ∀ {ℓ} {A : Set ℓ} (a : A) → Set ℓ
 UnitBridge a = R (λ { tt → a })

 data isTriv {ℓ} {A : Set ℓ} : (a : A) → UnitBridge a → Set ℓ where
   isTriv/ : (a : A) → isTriv a (pull (abort ⊤) (λ _ → a) (transport R (λ= abortLem) empty))

 isFunctional : ∀ {ℓ} {A : Set ℓ} {a a' : A} → Bridge a a' → Set ℓ
 isFunctional {A = A} {a} {a'} β = isTriv a (push takeFst β)

 compose : ∀ {ℓ} {A : Set ℓ} {a b c : A} → Bridge a b → Bridge b c → Bridge a c
 compose = {!!}

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
