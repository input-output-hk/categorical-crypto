{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Invariants of APROP-translated hypergraphs.
--
-- The canonical pruned `hCompose` (Option A) relies on structural properties
-- of the translation that are universal but not captured by the record
-- fields of `Hypergraph` alone. This module collects them.
--
-- CURRENT CONTENT:
--
--   * `hId-dom-covers A` — the identity hypergraph `hId A` has its `dom`
--     covering every vertex. Needed to show `count-non (hId A).dom ≡ 0`,
--     which lets the pruned `hComposeP (⟪f⟫) (hId B)` have the same vertex
--     count as `⟪f⟫` (key to discharging `idˡ`).
--
--   * `hId-cod-covers A` — the identity's `cod` also covers all vertices
--     (same proof, same structure).
--
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Invariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Prune
  using (AllIn; count-non; AllIn→count-non-zero)

open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

--------------------------------------------------------------------------------
-- Helper: every vertex of `G + K` is in `map injL G-dom ++ map injR K-dom`
-- provided the two sides individually cover. Phrased generically on lists.

private
  tensor-covers : ∀ {m n : ℕ} (xs : List (Fin m)) (ys : List (Fin n))
                → (∀ i → i ∈ xs) → (∀ j → j ∈ ys)
                → (∀ v → v ∈ map (inject+ n) xs ++ map (raise m) ys)
  tensor-covers {m} {n} xs ys cov-x cov-y v with splitAt m v in eq
  ... | inj₁ i = subst (_∈ _) (splitAt⁻¹-↑ˡ eq)
                       (∈-++⁺ˡ (∈-map⁺ (inject+ n) (cov-x i)))
  ... | inj₂ j = subst (_∈ _) (splitAt⁻¹-↑ʳ eq)
                       (∈-++⁺ʳ (map (inject+ n) xs) (∈-map⁺ (raise m) (cov-y j)))

--------------------------------------------------------------------------------
-- hId's dom (and cod) cover all vertices.

hId-dom-covers : ∀ A → AllIn (Hypergraph.dom (hId A))
hId-cod-covers : ∀ A → AllIn (Hypergraph.cod (hId A))

hId-dom-covers unit      = λ ()
hId-dom-covers (Var x)   = λ { zero → here refl }
hId-dom-covers (A ⊗₀ B) v =
  tensor-covers (Hypergraph.dom (hId A)) (Hypergraph.dom (hId B))
                (hId-dom-covers A) (hId-dom-covers B) v

hId-cod-covers unit      = λ ()
hId-cod-covers (Var x)   = λ { zero → here refl }
hId-cod-covers (A ⊗₀ B) v =
  tensor-covers (Hypergraph.cod (hId A)) (Hypergraph.cod (hId B))
                (hId-cod-covers A) (hId-cod-covers B) v

--------------------------------------------------------------------------------
-- Immediate corollary: `count-non (hId A).dom ≡ 0`. With the pruned
-- `hComposeP`, this means `hComposeP G (hId B)` has the same vertex count
-- as `G` (up to `+-identityʳ`) — the cornerstone of `idˡ`.

hId-count-non-dom : ∀ A → count-non (Hypergraph.dom (hId A)) ≡ 0
hId-count-non-dom A = AllIn→count-non-zero (hId-dom-covers A)

hId-count-non-cod : ∀ A → count-non (Hypergraph.cod (hId A)) ≡ 0
hId-count-non-cod A = AllIn→count-non-zero (hId-cod-covers A)
