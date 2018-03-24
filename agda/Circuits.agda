module Circuits where

open import HoTT

data Tp : Set where
  𝟙 𝟚 : Tp
  _•_ _⇒_ : Tp → Tp → Tp

∁ : Tp → Set
∁ 𝟙 = Unit
∁ 𝟚 = Bool
∁ (σ • τ) = ∁ σ × ∁ τ
∁ (σ ⇒ τ) = ∁ σ → ∁ τ

data § : Tp → Set where
 ret : {σ : Tp} → ∁ σ → § σ
 app : {σ τ : Tp} → § (σ ⇒ τ) → § σ → § τ
 reg : {σ : Tp} → § (𝟚 ⇒ (𝟚 • σ)) → § σ

readSeq : {σ τ : Tp} → § σ → ∁ (σ ⇒ τ) → § τ
readSeq s c = app (ret c) s

count : {σ : Tp} → § σ → Tp
count (ret x) = 𝟙
count (app s t) = count s • count t
count (reg x) = 𝟚 • count x

cvt : {σ : Tp} (s : § σ) → ∁ (count s) → (∁ (count s) × ∁ σ)
cvt (ret c) = λ tt → (tt , c)
cvt (app f x) = λ { (wf , wx) →
  let (of , cf) = cvt f wf in
  let (ox , cx) = cvt x wx in (of , ox) , cf cx }
cvt (reg x) (b , tl) =
  let (tl' , f) = cvt x tl in
  let (b' , c) = f b in (b , tl') , c

cvtΣ : {σ : Tp} → § σ → Σ Tp (λ ρ → ∁ ρ → (∁ ρ × ∁ σ))
cvtΣ s = count s , cvt s

Vec : (σ : Tp) (n : ℕ) → Tp
Vec σ O = 𝟙
Vec σ (S n) = σ • Vec σ n

Bits : (n : ℕ) → Tp
Bits n = Vec 𝟚 n

Map : {σ τ : Tp} {n : ℕ} → ∁ (σ ⇒ τ) → ∁ (Vec σ n) → ∁ (Vec τ n)
Map {n = O} f v = unit
Map {n = S n} f (h , tl) = (f h) , (Map f tl)

Register : (n : ℕ) (value : ∁ (Bits n)) (write : ∁ 𝟚) → § (Bits n)
Register O value write = ret tt
Register (S n) (vh , vtl) write = rv where
  tailReg = Register n vtl write
  rv : § (Bits (S n))
  rv = readSeq tailReg (λ oldtl → {!!})
  foo : Bool → Bool → (Bool × Bool × ∁ (Vec 𝟚 n))
  foo true rp = vh , vh , {!!}
  foo false rp = rp , rp , {!!}

nreg : {n : ℕ} {σ : Tp} → § (Bits n ⇒ (Bits n • σ)) → § σ
nreg {O} s = app (ret λ f → (f tt) .snd) s
nreg {S n} s = {!!}
