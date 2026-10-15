{-# OPTIONS --safe --without-K --guardedness #-}

-- A finite cover of all labelled successors is stronger than finiteness
-- separately at each fixed label when the visible alphabet is infinite.
module CategoricalCrypto.CSP.FiniteBranching (E B R : Set) where

open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.Product.Base

open import CategoricalCrypto.CSP.Process E B R

private variable
  p q : Tree
  l : Label

record FiniteSteps (p : Tree) : Set where
  field
    successors : List (Label × Tree)
    sound : (l , q) ∈ successors → p ─[ l ]→ q
    cover : p ─[ l ]→ q → (l , q) ∈ successors

record FinitelyBranching (p : Tree) : Set where
  coinductive
  field
    finite : FiniteSteps p
    after : p ─[ l ]→ q → FinitelyBranching q
