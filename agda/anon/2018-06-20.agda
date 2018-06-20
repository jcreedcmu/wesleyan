{-# OPTIONS --without-K --rewriting #-}
module 2018-06-20 where

open import HoTT

postulate
  Obj : Set
  Mor : Obj → Obj → Set
  idm : (d : Obj) → Mor d d

record Tp : Set₁ where
  constructor tp
  field
    Tob : Obj → Obj → Set
    Tmr : {d d' e e' : Obj} (f : Mor d d') (f' : Mor e' e) → Tob d e → Tob d' e'

_⇒_ : Tp → Tp → Tp
tp Aob Amr ⇒ tp Bob Bmr = tp
  (λ d e → Aob e d → Bob d e)
  (λ m n h → Bmr m n ∘ h ∘ Amr n m)

record End (t : Tp) : Set where
  constructor end
  open Tp t
  field
    Eob : (d : Obj) → Tob d d
    Ecnst : (d e : Obj) (f : Mor d e) →
      Tmr f (idm d) (Eob d) == Tmr (idm e) f (Eob e)

postulate
  idm/ident : (t : Tp) (d e : Obj) (x : Tp.Tob t d e) → Tp.Tmr t (idm d) (idm e) x == x

infixr 5 _⇒_

construct : (A B C Γ : Tp) → End (Γ ⇒ A) → End (Γ ⇒ B ⇒ C) → End (Γ ⇒ (A ⇒ B) ⇒ C)
construct A B C Γ (end Mob Mcnst) (end Nob Ncnst) = end
  (λ d g h → Nob d g (h (Mob d g))) endlem where
  endlem : (d e : Obj) (f : Mor d e) →
     Tp.Tmr (Γ ⇒ (A ⇒ B) ⇒ C) f (idm d) (λ g h → Nob d g (h (Mob d g)))
     ==
     Tp.Tmr (Γ ⇒ (A ⇒ B) ⇒ C) (idm e) f (λ g h → Nob e g (h (Mob e g)))
  endlem d e f =
    Tp.Tmr (Γ ⇒ (A ⇒ B) ⇒ C) f (idm d) (λ g h → Nob d g (h (Mob d g)))
    =⟨ idp ⟩
    (λ x x₁ →
         Tp.Tmr C f (idm d)
         (Nob d (Tp.Tmr Γ (idm d) f x)
          (Tp.Tmr B (idm d) f
           (x₁ (Tp.Tmr A f (idm d) (Mob d (Tp.Tmr Γ (idm d) f x)))))))
    =⟨ ap (λ z x x₁ → Tp.Tmr C f (idm d) (Nob d (Tp.Tmr Γ (idm d) f x)
             (Tp.Tmr B (idm d) f (x₁ (z x))))) (Mcnst d e f) ⟩
    (λ x x₁ →
         Tp.Tmr C f (idm d)
         (Nob d (Tp.Tmr Γ (idm d) f x)
          (Tp.Tmr B (idm d) f
           (x₁ (Tp.Tmr A (idm e) f (Mob e (Tp.Tmr Γ f (idm e) x)))))))
    =⟨ ap (λ z → λ x x₁ → z x (x₁ (Tp.Tmr A (idm e) f (Mob e (Tp.Tmr Γ f (idm e) x))))) (Ncnst d e f) ⟩
    ((λ x x₁ →
         Tp.Tmr C (idm e) f
         (Nob e (Tp.Tmr Γ f (idm e) x)
          (Tp.Tmr B f (idm e)
           (x₁ (Tp.Tmr A (idm e) f (Mob e (Tp.Tmr Γ f (idm e) x))))))))
    =⟨ idp ⟩
    Tp.Tmr (Γ ⇒ (A ⇒ B) ⇒ C) (idm e) f (λ g h → Nob e g (h (Mob e g)))
    =∎
