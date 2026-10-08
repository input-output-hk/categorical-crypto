{-# OPTIONS --safe --without-K #-}

module Data.Maybe.Ext where

open import Data.Bool.Base using (T; true)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_)

private
  variable
    a : Level
    A : Set a

-- Unlike the similarly named Any-based predicate, this lets ⊤'s eta discharge
-- an implicit witness when the search reduces to just. Eliminate the witness
-- with Data.Maybe.to-witness-T.
IsJust : Maybe A → Set
IsJust x = T (is-just x)

just≢nothing : {x : A} → just x ≢ nothing
just≢nothing ()

nothing≢just : {x : A} → nothing ≢ just x
nothing≢just ()

force! : (m : Maybe A) → is-just m ≡ true → A
force! (just x) _ = x
