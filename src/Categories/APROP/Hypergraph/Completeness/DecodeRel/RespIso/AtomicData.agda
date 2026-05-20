{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The `Atomic` predicate, factored out from `RespIso/Atomic.agda` so
-- that downstream modules (notably the Mac Lane discharge in
-- `AtomicCompound0E`) can reach it without dragging in the full
-- dispatcher module — which transitively imports `DecodeRoundtrip`'s
-- non-`--safe` postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AtomicData
  (sig : APROPSignature) where

open APROP sig

data Atomic : ∀ {A B} → HomTerm A B → Set where
  atomic-Agen : ∀ {A B} (g : mor A B) → Atomic (Agen g)
  atomic-id   : ∀ {A} → Atomic (id {A})
  atomic-λ⇒   : ∀ {A} → Atomic (λ⇒ {A})
  atomic-λ⇐   : ∀ {A} → Atomic (λ⇐ {A})
  atomic-ρ⇒   : ∀ {A} → Atomic (ρ⇒ {A})
  atomic-ρ⇐   : ∀ {A} → Atomic (ρ⇐ {A})
  atomic-α⇒   : ∀ {A B C} → Atomic (α⇒ {A} {B} {C})
  atomic-α⇐   : ∀ {A B C} → Atomic (α⇐ {A} {B} {C})
  atomic-σ    : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄ → Atomic (σ {A = A} {B = B} ⦃ s ⦄)
