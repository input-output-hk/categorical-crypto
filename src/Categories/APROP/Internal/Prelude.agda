{-# OPTIONS --safe --without-K #-}

module Categories.APROP.Internal.Prelude where

-- `splitAt` is `Data.Fin`'s in `Model/FromAPROP`, `zipWith` is `Data.Maybe.Base`'s
-- in `Solver/Split`.
open import Data.List public hiding (splitAt; zipWith)
import Data.List.Relation.Binary.Permutation.Propositional
import Data.List.Relation.Binary.Permutation.Propositional.Properties

-- Hiding `map` leaves `Data.List.map` unambiguous; `zip`/`zipWith` come from
-- `Data.List`.
open import Data.Product public
  hiding (assocʳ; assocˡ; map; map₁; map₂; map₂′; swap; _<*>_; zip; zipWith)

-- `[_]` clashes with `Data.List`'s; `Strict/Embed` defines a lemma `J` of its own.
open import Relation.Binary.PropositionalEquality public hiding (preorder; isPreorder; setoid; [_]; J)

open import Categories.APROP public
open import Categories.FreeMonoidal public

-- Redeclaring either alias in a consumer makes Agda report `AmbiguousName`,
-- even when both aliases denote the same module.
module Perm = Data.List.Relation.Binary.Permutation.Propositional
module PermProp = Data.List.Relation.Binary.Permutation.Propositional.Properties
