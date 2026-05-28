{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- FULL CONSTRUCTIVE DISCHARGE of `process-edges-resp-iso-stack`
-- from `CompletenessAssumptions` (`DecodeRespIso.agda` field (b)),
-- using the NEW `Perm.↭` signature (vs. the previously refuted `_≡_`).
--
-- ## Goal
--
-- Given `f, g : HomTerm A B` and an iso `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` at the
-- Translation (pruned) level, show:
--
--     map (Hypergraph.vlab ⟪ f ⟫F)
--         (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
--   Perm.↭
--     map (Hypergraph.vlab ⟪ g ⟫F)
--         (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
--
-- ## Status: FULL DISCHARGE (no postulates).
--
-- The proof is straightforward: both `⟪ f ⟫F` and `⟪ g ⟫F` are Linear
-- (`⟪⟫-Linear`), so `decode-attempt-Linear` proves each
-- `process-all-edges` succeeds with a final stack that is a
-- permutation of the respective `.cod`. Composing with the boundary
-- equation `map vlab .cod ≡ flatten B` (`⟪⟫F-codL`), we obtain:
--
--     map ⟪f⟫F.vlab (final-f) ↭ flatten B
--     map ⟪g⟫F.vlab (final-g) ↭ flatten B
--
-- Hence the two vlab-mapped stacks are permutations of each other
-- via transitivity through `flatten B`.
--
-- This is exactly the multiset-level statement the algorithm
-- guarantees, and it is the strongest list-level invariant derivable
-- from the iso (the corresponding `_≡_` statement was provably false:
-- see `Discharge/Sub/StackListEq.agda` counter-example
-- `Agen φ₁ ⊗ Agen φ₂` vs `σ ∘ (Agen φ₂ ⊗ Agen φ₁) ∘ σ`).
--
-- ## Relationship to `Discharge/StackEq.agda`
--
-- The companion file `Discharge/StackEq.agda` (written for the OLD
-- `_≡_` signature) contains essentially the same constructive
-- multiset proof under the name `stack-↭-from-iso`. With the field
-- signature now returning `Perm.↭`, that proof is the entire
-- discharge - no `StackEqAssumption` sub-postulate is needed.
--
-- This file is the clean repackaging for the corrected field.
--
-- ## Constructive helpers used
--
--   * `decode-attempt-Linear`         (Lin)         — totality of
--                                                     `decode-attempt`
--                                                     on `⟪ f ⟫F`.
--   * `decode-attempt-perm-from-just` (DecodeAttempt) — extract the
--                                                     final-stack
--                                                     `↭ .cod` witness.
--   * `⟪⟫F-codL`                      (FromAPROP)   — `codL ⟪ f ⟫F ≡
--                                                     flatten B`.
--   * `PermProp.map⁺`                 (stdlib)     — `_↭_` is
--                                                     preserved by `map`.
--   * `Perm.↭-reflexive`, `Perm.↭-sym`, `Perm.trans` (stdlib).
--
-- No constructive helpers from `LinearityIso.agda` are used: the iso
-- itself is consumed only to witness it exists; the bridge to a
-- common reference (`flatten B`) is established independently on each
-- side via boundary equations.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.StackPerm
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode-attempt-Linear; decode-attempt-perm-from-just)

open import Data.List using (map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong)

--------------------------------------------------------------------------------
-- ## Section 1: Per-side bridge to `flatten B`.
--
-- For any term `f : HomTerm A B`, the vlab-mapped final stack of
-- `process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)` is a permutation
-- of `flatten B`. Fully constructive.

stack-↭-flatten-B
  : ∀ {A B} (f : HomTerm A B)
  → map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    Perm.↭ flatten B
stack-↭-flatten-B f =
  let dal       = decode-attempt-Linear f
      perm-data = decode-attempt-perm-from-just ⟪ f ⟫F dal
      s_final   = proj₁ perm-data
      eq-proc   = proj₁ (proj₂ (proj₂ perm-data))
      s_↭_cod   = proj₂ (proj₂ (proj₂ perm-data))
      proj-eq : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
              ≡ s_final
      proj-eq = cong proj₁ eq-proc
      vlab-↭ : map (Hypergraph.vlab ⟪ f ⟫F) s_final
               Perm.↭ map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.cod ⟪ f ⟫F)
      vlab-↭ = PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫F) s_↭_cod
  in Perm.trans
       (Perm.↭-reflexive (cong (map (Hypergraph.vlab ⟪ f ⟫F)) proj-eq))
       (Perm.trans vlab-↭ (Perm.↭-reflexive (⟪⟫F-codL f)))

--------------------------------------------------------------------------------
-- ## Section 2: The discharge.
--
-- The top-level function with the exact signature of
-- `CompletenessAssumptions.process-edges-resp-iso-stack`.
--
-- The iso is consumed only for type-correctness; the conclusion
-- follows from each side's bridge to `flatten B` via transitivity.

process-edges-resp-iso-stack
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    Perm.↭
    map (Hypergraph.vlab ⟪ g ⟫F)
        (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
process-edges-resp-iso-stack f g _iso =
  Perm.trans (stack-↭-flatten-B f) (Perm.↭-sym (stack-↭-flatten-B g))
