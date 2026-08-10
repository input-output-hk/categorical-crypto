{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.Maybe`.
------------------------------------------------------------------------

module Data.Maybe.Ext where

open import Data.Bool.Base using (T)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)

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

-- `just x ≢ nothing`, as the absurd-pattern eliminator the `⊥-elim` sites
-- want.  stdlib 2.3 has no counterpart (`Data.Maybe.Properties` stops at
-- `just-injective`).
just≢nothing : {x : A} → just x ≡ nothing → ⊥
just≢nothing ()
