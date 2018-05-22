{-# OPTIONS --without-K --rewriting #-}
open import HoTT
open import 2018-05-22


module 2018-05-22-rewrites  where

{- Define rewriting rules for functoriality -}

module Abbrev (c d : Obj1) (f : Mor1 c d) where
  cf : Mor (c , d) (c , c)
  cf = (idm c , f)

  fd : Mor (c , d) (d , d)
  fd = (f , idm d)

  df : Mor (d , d) (d , c)
  df = (idm d , f)

  fc : Mor (c , c) (d , c)
  fc = (f , idm c)

  ff : Mor (c , d) (d , c)
  ff = (f , f)

module ALevel (c d : Obj1) (f : Mor1 c d) (a : oA (c , d)) where
  open Abbrev c d f
  postulate
    cred : mA fc (mA cf a) ↦ mA ff a
    dred : mA df (mA fd a) ↦ mA ff a
{-# REWRITE ALevel.cred #-}
{-# REWRITE ALevel.dred #-}

module BLevel (c d : Obj1) (f : Mor1 c d) (a : oA (c , d)) where
  open Abbrev c d f
  module B+ (b : oB+ (c , d) a) where
    postulate
      cred : mB+ fc (mA cf a) (mB+ cf a b) ↦ mB+ ff a b
      dred : mB+ df (mA fd a) (mB+ fd a b) ↦ mB+ ff a b
  module B- (b : oB- (c , d) (mA ff a)) where
    postulate
      cred : mB- fc a (mB- cf (mA cf a) b) ↦ mB- ff a b
      dred : mB- df a (mB- fd (mA fd a) b) ↦ mB- ff a b
{-# REWRITE BLevel.B+.cred #-}
{-# REWRITE BLevel.B+.dred #-}
{-# REWRITE BLevel.B-.cred #-}
{-# REWRITE BLevel.B-.dred #-}
