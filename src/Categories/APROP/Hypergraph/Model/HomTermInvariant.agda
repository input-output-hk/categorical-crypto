{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Translation-level invariant: for every APROP term `f : HomTerm A B`,
-- `⟪ f ⟫` has a `Unique` domain (and codomain) interface.
--
-- Used by the strict decoder's iso-invariance (`decodePˢ-resp-iso`) and the
-- ordering machinery (`IsoTransport`, `PartII`): the `Unique` interface
-- discharges the translated-term side conditions.
--
-- Structural induction on `f`: `hId`/`hSwap`/`hGen` cases from the matching
-- `Invariant` lemma; `_∘_`/`_⊗₁_` from `map⁺` + `++⁺`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Model.HomTermInvariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (module hComposeP-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-codL; ⟪⟫-domL)
open import Categories.APROP.Hypergraph.Model.Invariant sig
  using ( hId-dom-Unique; hSwap-dom-Unique; hGen-dom-Unique
        ; hId-cod-Unique; hSwap-cod-Unique; hGen-cod-Unique
        ; inject+-inj; raise-inj; disj-L-R)

open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Relation.Binary.PropositionalEquality using (sym; trans)

--------------------------------------------------------------------------------
-- `⟪ f ⟫.dom` is Unique for every APROP term.

⟪_⟫-dom-unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.dom ⟪ f ⟫)

⟪ Agen g ⟫-dom-unique = hGen-dom-Unique g

⟪ id {A} ⟫-dom-unique = hId-dom-Unique A

-- Composition: dom = map injL ⟪h⟫.dom, `injL` injective.
⟪ g ∘ h ⟫-dom-unique = Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫-dom-unique h)

-- Tensor: dom = map injL ⟪f⟫.dom ++ map injR ⟪g⟫.dom (disjoint).
⟪ f ⊗₁ g ⟫-dom-unique =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫-dom-unique f))
    (Uniq-Prop.map⁺ (raise-inj   _) (⟪_⟫-dom-unique g))
    (disj-L-R (Hypergraph.dom ⟪ f ⟫) (Hypergraph.dom ⟪ g ⟫))

-- Unitors / ρ / α: translated to `hId` directly.
⟪ λ⇒ {A} ⟫-dom-unique = hId-dom-Unique A
⟪ λ⇐ {A} ⟫-dom-unique = hId-dom-Unique A
⟪ ρ⇒ {A} ⟫-dom-unique = hId-dom-Unique (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫-dom-unique = hId-dom-Unique (A ⊗₀ unit)
⟪ α⇒ {A} {B} {C} ⟫-dom-unique = hId-dom-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A} {B} {C} ⟫-dom-unique = hId-dom-Unique ((A ⊗₀ B) ⊗₀ C)

⟪ σ {A} {B} ⟫-dom-unique = hSwap-dom-Unique A B

--------------------------------------------------------------------------------
-- `⟪ f ⟫.cod` is Unique for every APROP term.  The `g ∘ h` case shows
-- `Unique (map remapP ⟪g⟫.cod)` via `remap-injective`: `remapP` is globally
-- injective when `⟪g⟫.dom` is Unique (`⟪_⟫-dom-unique`) and `⟪h⟫.cod` is
-- Unique (the IH).

⟪_⟫-cod-unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.cod ⟪ f ⟫)

⟪ Agen g ⟫-cod-unique = hGen-cod-Unique g

⟪ id {A} ⟫-cod-unique = hId-cod-Unique A

-- Composition: cod = map remapP ⟪g⟫.cod, `remapP` globally injective from the
-- `Unique` boundaries (shared `PrunedCompose.remapP-injective-from-unique`).
⟪ g ∘ h ⟫-cod-unique =
  Uniq-Prop.map⁺
    (hCP.remapP-injective-from-unique (⟪_⟫-cod-unique h) (⟪_⟫-dom-unique g))
    (⟪_⟫-cod-unique g)
  where
    bdy = trans (⟪⟫-codL h) (sym (⟪⟫-domL g))
    module hCP = hComposeP-impl ⟪ h ⟫ ⟪ g ⟫ bdy

-- Tensor: cod = map injL ⟪f⟫.cod ++ map injR ⟪g⟫.cod (disjoint).
⟪ f ⊗₁ g ⟫-cod-unique =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫-cod-unique f))
    (Uniq-Prop.map⁺ (raise-inj   _) (⟪_⟫-cod-unique g))
    (disj-L-R (Hypergraph.cod ⟪ f ⟫) (Hypergraph.cod ⟪ g ⟫))

-- Unitors / ρ / α: translated to `hId`.
⟪ λ⇒ {A} ⟫-cod-unique = hId-cod-Unique A
⟪ λ⇐ {A} ⟫-cod-unique = hId-cod-Unique A
⟪ ρ⇒ {A} ⟫-cod-unique = hId-cod-Unique (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫-cod-unique = hId-cod-Unique (A ⊗₀ unit)
⟪ α⇒ {A} {B} {C} ⟫-cod-unique = hId-cod-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A} {B} {C} ⟫-cod-unique = hId-cod-Unique ((A ⊗₀ B) ⊗₀ C)

⟪ σ {A} {B} ⟫-cod-unique = hSwap-cod-Unique A B
