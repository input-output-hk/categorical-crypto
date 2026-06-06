{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Translation-level invariant: for every APROP term `f : HomTerm A B`,
-- `⟪ f ⟫` has a `Unique` domain (and codomain) interface.
--
-- Used by the composition congruence `hComposeP-resp-≅ᴴ` (the `Unique
-- K₁.dom` side condition is met when K₁ is a translated term).
--
-- Structural induction on `f`: `hId`/`hSwap`/`hGen` cases from the matching
-- `Invariant` lemma; `_∘_`/`_⊗₁_` from `map⁺` + `++⁺`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.HomTermInvariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hGen; hSwap)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Invariant sig
  using ( hId-dom-Unique; hSwap-dom-Unique; hGen-dom-Unique
        ; hId-cod-Unique; hSwap-cod-Unique; hGen-cod-Unique
        ; inject+-inj; raise-inj; disj-L-R)
open import Categories.APROP.Hypergraph.Prune
  using (remap-injective; lookup-injective-unique; nonMem-Unique)

open import Data.Fin using (Fin; inject+; raise)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; subst₂)

--------------------------------------------------------------------------------
-- `⟪ f ⟫.dom` is Unique for every APROP term.

⟪_⟫-dom-unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.dom ⟪ f ⟫)

⟪ Agen g ⟫-dom-unique = hGen-dom-Unique g

⟪ id {A} ⟫-dom-unique = hId-dom-Unique A

-- Composition: dom = map injL ⟪h⟫.dom, `injL` injective.
⟪ g ∘ h ⟫-dom-unique =
  Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫-dom-unique h)

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

-- Composition: cod = map remapP ⟪g⟫.cod, `remapP` globally injective.
⟪ g ∘ h ⟫-cod-unique =
  Uniq-Prop.map⁺ remapP-inj (⟪_⟫-cod-unique g)
  where
    open import Data.Fin using (cast)
    open import Data.Fin.Properties using (toℕ-cast; toℕ-injective)
    open import Relation.Binary.PropositionalEquality using (trans; cong)
    open import Categories.APROP.Hypergraph.Translation sig using (⟪⟫-codL; ⟪⟫-domL)

    bdy = trans (⟪⟫-codL h) (sym (⟪⟫-domL g))
    module hCP = hComposeP-impl ⟪ h ⟫ ⟪ g ⟫ bdy

    open import Data.Nat using (ℕ)
    cast-inj : ∀ {i j} → cast hCP.dom-cod-len i ≡ cast hCP.dom-cod-len j → i ≡ j
    cast-inj {i} {j} eq = toℕ-injective
      (trans (sym (toℕ-cast hCP.dom-cod-len i))
             (trans (cong (Data.Fin.toℕ) eq) (toℕ-cast hCP.dom-cod-len j)))
      where open import Data.Fin

    lookup-cod-inj : ∀ {i j} → hCP.lookup-cod i ≡ hCP.lookup-cod j → i ≡ j
    lookup-cod-inj {i} {j} eq =
      cast-inj (lookup-injective-unique (⟪_⟫-cod-unique h) _ _ eq)

    remapP-inj : ∀ {i j} → hCP.remapP i ≡ hCP.remapP j → i ≡ j
    remapP-inj eq =
      remap-injective _ _ (⟪_⟫-dom-unique g) lookup-cod-inj eq

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
