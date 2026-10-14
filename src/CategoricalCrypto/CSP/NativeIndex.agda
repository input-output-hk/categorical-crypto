{-# OPTIONS --safe --without-K #-}

-- Constructive tags for the used ExtI indices at agda-cardano-common
-- 9a40d1de330f376c3a102e7c9f1282f4fa830a7e. The index cannot depend on
-- the synchronization predicate: interchange uses several operators on it.
module CategoricalCrypto.CSP.NativeIndex (E B : Set) where

open import Data.Bool.Base

data Index : Set where
  raw : B → Index
  left right : Index → Index
  silence : Index
  commitment : Bool → Index
  concealed : E → Index
