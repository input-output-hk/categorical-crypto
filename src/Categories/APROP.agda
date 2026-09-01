{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- APROP (Autonomous PROP) term language, following TensorRocq
-- (arXiv:2604.17592). Thin wrapper around `Categories.FreeMonoidal`
-- specialised to `v = Symm`: the free symmetric monoidal category over a
-- signature `(X , mor)` of atoms and generators.
--
-- Define a signature `mySig : APROPSignature` and `open APROP mySig` to
-- access the term constructors. The generator injection is exposed as
-- `Agen` to match the paper's notation (elsewhere `var`).
--------------------------------------------------------------------------------

module Categories.APROP where

open import Categories.FreeMonoidal public

-- Propositional equality for the whole APROP tree: 47 of the 53 modules that
-- blanket-open this one imported it themselves.  The hidden names are the four
-- the island prelude hides (`[_]` clashes with `Data.List`'s) plus `J`, which
-- `Strict/Embed` defines as a lemma of its own — a name this re-export would
-- otherwise make undefinable there.
open import Relation.Binary.PropositionalEquality public
  hiding (preorder; isPreorder; setoid; [_]; J)

-- `Data.List` for the whole tree: 46 of the 52 blanket-openers imported it
-- themselves, 44 of them with a `using` list.  Only two names are hidden, and
-- in both cases because a scope module wants a DIFFERENT module's function of
-- that name: `splitAt` is `Data.Fin`'s in `Model/FromAPROP`, and `zipWith` is
-- `Data.Maybe.Base`'s in `Solver/Split`.
open import Data.List public
  hiding (splitAt; zipWith)

-- `Data.Product` likewise, for 36 of the openers, all with a `using` list;
-- between them they need only `_,_`, `proj₁`, `proj₂`, `Σ`, `Σ-syntax`,
-- `∃-syntax` and `_×_`.  Eight of the hidden names are the ones
-- `categorical-crypto.Prelude` hides for this same module; `zip`/`zipWith`
-- join them because the `Data.List` re-export above already binds them.
-- NOTE this list is load bearing for that re-export: hiding `map` here is what
-- leaves `Data.List.map`, which 25 scope modules use, unambiguous.
open import Data.Product public
  hiding (assocʳ; assocˡ; map; map₁; map₂; map₂′; swap; _<*>_; zip; zipWith)

-- `Perm` as a re-exported module ALIAS: 36 of the 52 modules that blanket-open
-- this one spell exactly
-- `import Data.List.Relation.Binary.Permutation.Propositional as Perm`.
-- An alias adds no unqualified name, so unlike the re-export above it cannot
-- make a use site ambiguous — but every sibling alias of the name must go,
-- including indented and multi-line spellings, or Agda reports an
-- `AmbiguousName` between two aliases denoting the same module.
import Data.List.Relation.Binary.Permutation.Propositional
module Perm = Data.List.Relation.Binary.Permutation.Propositional

-- `PermProp` likewise, for 25 of the same modules.
import Data.List.Relation.Binary.Permutation.Propositional.Properties
module PermProp = Data.List.Relation.Binary.Permutation.Propositional.Properties

record APROPSignature : Set₁ where
  field X : Set

  open FreeMonoidalHelper Symm X using (ObjTerm)

  field mor : ObjTerm → ObjTerm → Set

  asFreeMonoidalData : FreeMonoidalData
  asFreeMonoidalData = record { v = Symm ; X = X ; mor = mor }

module APROP (sig : APROPSignature) where
  open APROPSignature sig public
  open FreeMonoidal asFreeMonoidalData public renaming (var to Agen)

  -- `Symm ≤ Symm` for instance search, so `σ` needs no explicit `⦃ v≤v ⦄`.
  instance
    Symm≤Symm : Symm ≤ Symm
    Symm≤Symm = v≤v
