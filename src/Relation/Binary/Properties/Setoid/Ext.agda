{-# OPTIONS --safe --without-K #-}

open import Function.Bundles
open import Function.Properties.Equivalence using (⇔-setoid)
open import Relation.Binary.Bundles

module Relation.Binary.Properties.Setoid.Ext {a ℓ} (S : Setoid a ℓ) where

open Setoid S

∼[_] : Carrier → Func S (⇔-setoid ℓ)
∼[ r ] = record { to = r ≈_ ; cong = λ h → mk⇔ (λ k → trans k h) (λ k → trans k (sym h)) }
