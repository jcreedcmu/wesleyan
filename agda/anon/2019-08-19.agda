module 2019-08-19 where

open import HoTT hiding (S ; _+_)

_+_ = _⊔_

State : Set → Set → Set
State S X = S → (X × S)

Cont : Set → Set → Set
Cont R X = (X → R) → R

Exn : Set → Set → Set
Exn E X = X + E

state-cont : {S X R : Set} → Cont R (State S X) → State S (Cont R X)
state-cont k s =  (λ f → k (λ t → f (fst (t s)))) , s

-- cont-state : {S X R : Set} → State S (Cont R X) → Cont R (State S X)
-- cont-state σ t = t (λ s → {!fst (σ s)!} , (snd (σ s)))

state-exn : {S X E : Set} → Exn E (State S X) → State S (Exn E X)
state-exn (inl x) s = (inl (fst (x s))) , snd (x s)
state-exn (inr x) s = (inr x) , s

cont-exn : {R X E : Set} → Exn E (Cont R X) → Cont R (Exn E X)
cont-exn (inl f) y = f (λ x → y (inl x))
cont-exn (inr x) y = y (inr x)
