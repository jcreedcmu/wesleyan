{-# OPTIONS --without-K #-}
open import HoTT

module 2018-09-02b where

record Conv1 {n1 n0}
  {I1 : Set n1} {I0 : Set n0}
  (R : I1 → I0 → Set)
  (A1 : I1 → Set)
  (i0 : I0) : Set (lmax n1 n1)
  where
  constructor conv1
  field
    i1 : I1
    p1 : A1 i1
    r : R i1 i0

record Conv2 {n1 n2 n0}
  {I1 : Set n1} {I2 : Set n2} {I0 : Set n0}
  (R : I1 → I2 → I0 → Set)
  (A1 : I1 → Set) (A2 : I2 → Set)
  (i0 : I0) : Set (lmax n1 n2)
  where
  constructor conv2
  field
    i1 : I1
    i2 : I2
    p1 : A1 i1
    p2 : A2 i2
    r : R i1 i2 i0

_a×_ : ∀ {n} {I : Set n} → (I → Set) → (I → Set) → I → Set
(A a× B)(α) = A α × B α

-- record Series (A : Sset) (α : Set) : Set₁ where
--   constructor ser
--   field
--     n : Set
--     dat : n → α
--     coef : A n

-- _s×_ : Sset → Sset → Sset
-- (A s× B)(α) = A α × B α

-- cop : {A B C : Set} → (A → C) → (B → C) → A ⊔ B → C
-- cop f g (inl x) = f x
-- cop f g (inr x) = g x

-- copη : {A B C : Set} (dat : A ⊔ B → C) → cop (dat ∘ inl) (dat ∘ inr) ∼ dat
-- copη dat (inl x) = idp
-- copη dat (inr x) = idp

lemma : ∀ {n1 n2 n0}
  {I1 : Set n1} {I2 : Set n2} {I0 : Set n0}
  (R : I1 → I2 → I0 → Set)
  (A1 : I1 → Set) (A2 : I2 → Set)
  (i0 : I0) → Set (lmax n1 n2)
  → Set
lemma = ?

-- lemma : (A B : Sset) → Series (A ⊗ B) ∼ (Series A s× Series B)
-- lemma A B α = ua (equiv into out zig zag) where
--   into : (x : Series (A ⊗ B) α) → Σ (Series A α) (λ _ → Series B α)
--   out : (x : Σ (Series A α) (λ _ → Series B α)) → Series (A ⊗ B) α
--   into (ser n dat (ten x y pA pB pS)) =
--     (ser x (dat ∘ (coe pS) ∘ inl) pA) ,
--     (ser y (dat ∘ (coe pS) ∘ inr) pB)
--   out (ser x dat coef , ser y dat₁ coef₁) = ser (x ⊔ y) (cop dat dat₁)
--       (ten x y coef coef₁ idp)
--   zig : (x : Σ (Series A α) (λ _ → Series B α)) → into (out x) == x
--   zig (ser x dat coef , ser y dat₁ coef₁) = idp

--   zag : (x : Series (A ⊗ B) α) → out (into x) == x
--   zag (ser n dat (ten x y pA pB pS)) = lem pS where
--     lem : (pS : x ⊔ y == n) → ser (Coprod x y)
--         (cop (λ x₁ → dat (coe pS (inl x₁))) (λ x₁ → dat (coe pS (inr x₁))))
--         (ten x y pA pB idp) == ser n dat (ten x y pA pB pS)
--     lem idp = ap (λ z → ser (Coprod x y) z (ten x y pA pB idp)) (λ= (copη dat))

-- thm : (A B : Sset) → Series (A ⊗ B) == (Series A s× Series B)
-- thm A B = λ= (lemma A B)

-- -- {-# OPTIONS --without-K #-}
-- -- open import HoTT

-- -- module 2018-09-02 where

-- -- Nset : Set₁
-- -- Nset = ℕ → Set

-- -- Sset : Set₂
-- -- Sset = Set → Set₁

-- -- record _⊗_ (A B : Sset) (n : Set) : Set₁ where
-- --   constructor ten
-- --   field
-- --     x y : Set
-- --     pA : A x
-- --     pB : B y
-- --     pS : x ⊔ y == n

-- -- record Fprop : Set₁ where
-- --   constructor fp
-- --   field
-- --     p : Set → Set
-- --     pres : {A B : Set} → p (A ⊔ B) == p A × p B

-- -- record Series (P : Fprop) (A : Sset) (α : Set) : Set₁ where
-- --   constructor ser
-- --   field
-- --     n : Set
-- --     hasProp : Fprop.p P n
-- --     dat : n → α
-- --     coef : A n

-- -- _s×_ : Sset → Sset → Sset
-- -- (A s× B)(α) = A α × B α

-- -- cop : {A B C : Set} → (A → C) → (B → C) → A ⊔ B → C
-- -- cop f g (inl x) = f x
-- -- cop f g (inr x) = g x

-- -- copη : {A B C : Set} (dat : A ⊔ B → C) → cop (dat ∘ inl) (dat ∘ inr) ∼ dat
-- -- copη dat (inl x) = idp
-- -- copη dat (inr x) = idp

-- -- lemma : (A B : Sset) (P : Fprop) → Series P (A ⊗ B) ∼ (Series P A s× Series P B)
-- -- lemma A B P α = ua (equiv into out zig zag) where
-- --   into : (x : Series P (A ⊗ B) α) → Σ (Series P A α) (λ _ → Series P B α)
-- --   out : (x : Σ (Series P A α) (λ _ → Series P B α)) → Series P (A ⊗ B) α
-- --   into (ser n hasProp dat (ten x y pA pB pS)) =
-- --     (ser x {!!} (dat ∘ (coe pS) ∘ inl) pA) ,
-- --     (ser y {!!} (dat ∘ (coe pS) ∘ inr) pB)
-- --   out (ser x hasProp dat coef , ser y hasProp₁ dat₁ coef₁) =
-- --       ser (x ⊔ y) {!!} (cop dat dat₁)
-- --       (ten x y coef coef₁ idp)
-- --   zig : (x : Σ (Series P A α) (λ _ → Series P B α)) → into (out x) == x
-- --   zig (ser x hasProp dat coef , ser y hasProp₁ dat₁ coef₁) = idp

-- --   zag : (x : Series P (A ⊗ B) α) → out (into x) == x
-- --   zag (ser n hasProp dat (ten x y pA pB pS)) = lem pS where
-- --     lem : (pS : x ⊔ y == n) → ser (Coprod x y) {!!}
-- --         (cop (λ x₁ → dat (coe pS (inl x₁))) (λ x₁ → dat (coe pS (inr x₁))))
-- --         (ten x y pA pB idp) == ser n {!!} dat (ten x y pA pB pS)
-- --     lem idp = ap (λ z → ser (Coprod x y) {!!} z (ten x y pA pB idp)) (λ= (copη dat))

-- -- thm : (A B : Sset) (P : Fprop) → Series P (A ⊗ B) == (Series P A s× Series P B)
-- -- thm A B P = λ= (lemma A B P)
