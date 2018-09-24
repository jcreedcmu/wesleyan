{-# OPTIONS --without-K --rewriting #-}

module ConstructingTypes where

open import HoTT hiding (_∙_ )
open import CategoryVariables using (Del)

module Main (Δ : Del) where
  open CategoryVariables.Main Δ
