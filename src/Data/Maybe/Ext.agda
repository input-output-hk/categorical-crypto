{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.Maybe`.
------------------------------------------------------------------------

module Data.Maybe.Ext where

open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Level
open import Relation.Binary.PropositionalEquality

private
  variable
    a : Level
    A : Set a

-- `T ∘ is-just`: a `Set` that normalises to `⊤` on `just` and to `⊥` on
-- `nothing`.  Unlike the `Any`-based `Data.Maybe.Is-just` it computes, so an
-- implicit `{IsJust x}` is auto-discharged (by `⊤`'s eta) exactly when `x`
-- reduces to a `just`.  Eliminate it with `Data.Maybe.to-witness-T`.
IsJust : Maybe A → Set
IsJust x = T (is-just x)

just≢nothing : {x : A} → just x ≢ nothing
just≢nothing ()

nothing≢just : {x : A} → nothing ≢ just x
nothing≢just ()
