{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.Maybe`.
------------------------------------------------------------------------

module Data.Maybe.Ext where

open import Data.Bool.Base using (T)
open import Data.Maybe.Base using (Maybe; is-just)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

-- `T ∘ is-just`: a `Set` that NORMALISES to `⊤` on `just` and to `⊥` on
-- `nothing`.  Unlike the `Any`-based `Data.Maybe.Is-just` it computes, so an
-- implicit `{IsJust x}` is auto-discharged (by `⊤`'s eta) exactly when `x`
-- reduces to a `just`.  Eliminate it with `Data.Maybe.to-witness-T`.
IsJust : Maybe A → Set
IsJust x = T (is-just x)
