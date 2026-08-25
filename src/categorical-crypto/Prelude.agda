{-# OPTIONS --safe --without-K #-}

module categorical-crypto.Prelude where

open import Agda.Primitive using () renaming (Set to Type) public

open import Level public
  hiding (lower; _⊔_)
  renaming (suc to sucˡ; zero to zeroˡ)
open import Function public

open import Data.Bool public
  hiding (_≟_; _≤_; _≤?_; _<_; _<?_; if_then_else_)
open import Data.Empty public
open import Data.List public
  hiding (align; alignWith; filter; fromMaybe; map; zip; zipWith)
open import Data.Maybe public
  hiding (_>>=_; align; alignWith; ap; fromMaybe; map; zip; zipWith)
open import Data.Unit public
  using (⊤; tt)
open import Data.Sum public
  hiding (assocʳ; assocˡ; map; map₁; map₂; reduce; swap)
open import Data.Product public
  hiding (assocʳ; assocˡ; map; map₁; map₂; map₂′; swap; _<*>_)
open import Data.Nat public
  hiding (_≟_; _≤_; _≤?_; _<_; _<?_; _≤ᵇ_; _≡ᵇ_; _≥_; _>_; _+_
         ; less-than-or-equal)

open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality public
  hiding (preorder; isPreorder; setoid; [_])

open import Class.Functor public
  renaming (fmap to map)
open import Class.Monad public
open import Class.DecEq public
open import Class.Decidable public
