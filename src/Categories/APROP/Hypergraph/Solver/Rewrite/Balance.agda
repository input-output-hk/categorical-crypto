{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Balanced reassociation `reassocBal`, the context normaliser of the deep
-- rewrite frames (`Solver.Frontend.Rewrite`).  Assoc-only and unverified: the
-- frames it builds are re-certified by `findIsoᵀ`, so it needs no soundness
-- proof, only to preserve the hypergraph up to isomorphism.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Rewrite.Balance (sig : APROPSignature) where

open import Categories.APROP.Internal.Prelude

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

open APROP sig

--------------------------------------------------------------------------------
-- Balancing the composition spine makes frame construction logarithmic in
-- depth instead of linear.
--------------------------------------------------------------------------------

private
  variable
    A B C D : ObjTerm

  -- Star reads HomTerm backwards: the head is the last-applied factor.
  Chain : ObjTerm → ObjTerm → Set
  Chain A B = Star (λ Y Z → HomTerm Z Y) B A

  lenC : Chain A B → ℕ
  lenC ε        = 0
  lenC (_ ◅ gs) = suc (lenC gs)

  pairC : Chain A B → Chain A B
  pairC ε              = ε
  pairC (h ◅ ε)        = h ◅ ε
  pairC (h ◅ (g ◅ gs)) = (h ∘ g) ◅ pairC gs

  balC : ℕ → Chain A B → HomTerm A B
  balC _       ε        = id
  balC _       (f ◅ ε)  = f
  -- The fuel-exhausted fallback right-collapses; unreachable with fuel = length.
  balC zero    (g ◅ gs) = fold (λ Y Z → HomTerm Z Y) _∘_ id (g ◅ gs)
  balC (suc n) (g ◅ gs) = balC n (pairC (g ◅ gs))

  -- Removing identities avoids edge-free hComposeP seams; their endpoint
  -- equality leaves the tail at the required type.
  dropIdC : Chain A B → Chain A B
  dropIdC ε           = ε
  dropIdC (id   ◅ gs) = dropIdC gs
  dropIdC (g    ◅ gs) = g ◅ dropIdC gs

  -- All-identity tensors differ from hId only by allFin-++ reindexing, so
  -- collapsing them preserves the downstream isomorphism gate.
  isIdᵗ : HomTerm A B → Maybe (A ≡ B)
  isIdᵗ id        = just refl
  isIdᵗ (f ⊗₁ g) with isIdᵗ f | isIdᵗ g
  ... | just refl | just refl = just refl
  ... | _         | _         = nothing
  isIdᵗ _         = nothing

  -- Decode's coherence bridges meet inverse bridges at seams. Cancel from
  -- right to left, looking again after each cancellation to catch cascades.
  cancelC : Chain A B → Chain A B
  cancelC ε          = ε
  cancelC (g ◅ gs)   = step g (cancelC gs)
    where
      step : HomTerm B C → Chain A B → Chain A C
      step α⇒ (α⇐ ◅ gs) = gs
      step α⇐ (α⇒ ◅ gs) = gs
      step λ⇒ (λ⇐ ◅ gs) = gs
      step λ⇐ (λ⇒ ◅ gs) = gs
      step ρ⇒ (ρ⇐ ◅ gs) = gs
      step ρ⇐ (ρ⇒ ◅ gs) = gs
      step (σ ⦃ _ ⦄) ((σ ⦃ _ ⦄) ◅ gs) = id ◅ gs
      step g  gs        = g ◅ gs

mutual
  flat∘ : HomTerm A B → Chain A B
  flat∘ (g ∘ f)  = flat∘ g ◅◅ flat∘ f
  flat∘ (f ⊗₁ g) = tensorLeaf (reassocBal f) (reassocBal g)
  flat∘ f        = f ◅ ε

  tensorLeaf : HomTerm A C → HomTerm B D → Chain (A ⊗₀ B) (C ⊗₀ D)
  tensorLeaf f g with isIdᵗ f | isIdᵗ g
  ... | just refl | just refl = id ◅ ε
  ... | _         | _         = (f ⊗₁ g) ◅ ε

  reassocBal : HomTerm A B → HomTerm A B
  reassocBal f = let c = dropIdC (cancelC (dropIdC (flat∘ f))) in balC (lenC c) c
