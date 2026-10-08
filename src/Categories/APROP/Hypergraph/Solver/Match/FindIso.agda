{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Sound but incomplete isomorphism search: fuel exhaustion or conservative
-- label matching may reject an isomorphic pair.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Match.FindIso (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Model.Iso
open import Categories.APROP.Hypergraph.Solver.Match.PBij
open import Categories.APROP.Hypergraph.Solver.Match.Search sig
open import Categories.APROP.Hypergraph.Solver.Match.Verify sig
open import Categories.APROP.Hypergraph.Solver.Tabulate

open import Data.Maybe.Base as Maybe
import Data.Nat.Properties as Nat
open import Data.Product
open import Relation.Nullary using (yes; no)

-- Seed labels need no separate check: Search compares endpoint labels and
-- Verify checks every vertex, so a seed-time sweep only duplicates work.

seedFromInterfaces : (H J : Hypergraph FlatGen)
                   → Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
seedFromInterfaces H J =
  pairUp emptyBij (Hypergraph.dom H) (Hypergraph.dom J) >>= λ b →
  pairUp b        (Hypergraph.cod H) (Hypergraph.cod J)

findIso : ∀ (H J : Hypergraph FlatGen) → Maybe (H ≅ᴴ J)
findIso H J with Hypergraph.nV H Nat.≟ Hypergraph.nV J
... | no _ = nothing
... | yes _ with Hypergraph.nE H Nat.≟ Hypergraph.nE J
...   | no _ = nothing
...   | yes _ =
  seedFromInterfaces H J             >>= λ φ₀ →
  searchIso H J φ₀ emptyBij          >>= λ { (φ , ψ) →
  Verify.verify H J φ ψ }

-- Tabulation shares field results (see Solver.Tabulate). Consumers inspecting
-- only is-just do not force the transport's isomorphism proof fields.
findIsoᵀ : (H J : Hypergraph FlatGen) → Maybe (H ≅ᴴ J)
findIsoᵀ H J =
  Maybe.map
    (λ iso → trans-≅ᴴ (sym-≅ᴴ (tab-≅ᴴ H)) (trans-≅ᴴ iso (tab-≅ᴴ J)))
    (findIso (tabH H) (tabH J))
