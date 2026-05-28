{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic "Steps" infrastructure over a FreeMonoidalData with Symm ≤ v.
--
-- This module mirrors the APROP-specific machinery in
-- `Categories/APROP/Hypergraph/Completeness/{Decode,Permute,Unflatten}.agda`
-- and `.../Discharge/Sub/ProcessTermAligned.agda`, but strips out:
--
--   * `Hypergraph FlatGen` (uses `Steps` directly).
--   * `vlab : Fin nV → X` (stacks live in `List X` directly).
--   * `extract-prefix` (AllFire's locating witness IS the permutation).
--
-- The result is the Sense-1 form of the c'-chain primitives:
-- pure free symmetric monoidal category, parameterised only over the
-- atoms `X` and the morphism family `mor`.
--
-- Used by `Categories.FreeSMC.MacLaneAtoms`.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.Steps
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

-- Generic `unflatten` and `permute` (already defined parametrically there).
open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; permute) public

open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (_⊗ᵢ_)
open import Categories.Category.Monoidal using (Monoidal)
open Monoidal Monoidal-FreeMonoidal using (unitorˡ; unitorʳ; associator)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅)

open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

--------------------------------------------------------------------------------
-- `unflatten-++-≅`: `unflatten` distributes over `_++_` up to coherence.
-- Same definition as `Categories.APROP.Hypergraph.Completeness.Unflatten`,
-- lifted to the generic setting.

unflatten-++-≅
  : ∀ (xs ys : List X)
  → unflatten (xs ++ ys) ≅ unflatten xs ⊗₀ unflatten ys
unflatten-++-≅ []       ys = ≅.sym unitorˡ
unflatten-++-≅ (x ∷ xs) ys =
  ≅.trans (≅.refl ⊗ᵢ unflatten-++-≅ xs ys) (≅.sym associator)

--------------------------------------------------------------------------------
-- A "step": typed morphism between unflattened input/output lists.

Step : Set
Step = Σ[ ein ∈ List X ] Σ[ eout ∈ List X ]
       HomTerm (unflatten ein) (unflatten eout)

Steps : Set
Steps = List Step

-- Field projections.
ein-of : Step → List X
ein-of (ein , _ , _) = ein

eout-of : Step → List X
eout-of (_ , eout , _) = eout

op-of : (s : Step) → HomTerm (unflatten (ein-of s)) (unflatten (eout-of s))
op-of (_ , _ , op) = op

--------------------------------------------------------------------------------
-- Apply one step at the front of a stack, given the locating permutation.

fire-bridged
  : ∀ (e : Step) (s rest : List X)
  → s Perm.↭ ein-of e ++ rest
  → HomTerm (unflatten s) (unflatten (eout-of e ++ rest))
fire-bridged (ein , eout , op) s rest perm =
  (_≅_.to   (unflatten-++-≅ eout rest)
   ∘ (op ⊗₁ id)
   ∘ _≅_.from (unflatten-++-≅ ein rest))
  ∘ permute perm

--------------------------------------------------------------------------------
-- AllFire: each step's input list is locatable in the running stack.
--
-- Witness shape is (rest, perm, tail-AllFire).  Unlike the APROP version,
-- there is no `extract-prefix ≡ just …` requirement: the perm IS the
-- locating witness.

AllFire : Steps → List X → Set
AllFire []                       _ = ⊤
AllFire ((ein , eout , _) ∷ es) s =
  Σ[ rest ∈ List X ]
  Σ[ p ∈ s Perm.↭ ein ++ rest ]
    AllFire es (eout ++ rest)

--------------------------------------------------------------------------------
-- IndependentSwap: both orderings AllFire.

IndependentSwap : Step → Step → List X → Set
IndependentSwap e₁ e₂ s =
  AllFire (e₁ ∷ e₂ ∷ []) s × AllFire (e₂ ∷ e₁ ∷ []) s

--------------------------------------------------------------------------------
-- Process a step list under an AllFire witness.  Returns (final stack,
-- composed morphism).

process-steps
  : (es : Steps) (s : List X) → AllFire es s
  → Σ[ s' ∈ List X ] HomTerm (unflatten s) (unflatten s')
process-steps []                       s _                   = (s , id)
process-steps ((ein , eout , op) ∷ es) s (rest , perm , af) =
  let (s' , t) = process-steps es (eout ++ rest) af
  in  (s' , t ∘ fire-bridged (ein , eout , op) s rest perm)

--------------------------------------------------------------------------------
-- ProcessEdges↭Goal: stack permutation + term equation between two
-- AllFire orderings of step lists with the same starting stack.

ProcessEdges↭Goal
  : (es₁ es₂ : Steps) (s : List X)
    (af₁ : AllFire es₁ s) (af₂ : AllFire es₂ s)
  → Set
ProcessEdges↭Goal es₁ es₂ s af₁ af₂ =
  Σ[ stack-↭ ∈
      proj₁ (process-steps es₁ s af₁)
      Perm.↭
      proj₁ (process-steps es₂ s af₂) ]
    proj₂ (process-steps es₁ s af₁)
    ≈Term
    permute (Perm.↭-sym stack-↭) ∘ proj₂ (process-steps es₂ s af₂)
