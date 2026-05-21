{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Route 1 viability test (see REFACTORING.md § "Route 1").
--
-- The missing core lemma for an iso-invariant decoder is `process-edges-↭`:
-- given two edge sequences related by `_↭_`, the resulting final-stacks are
-- `_↭_`-related AND the resulting morphisms are `_≈Term_`-equivalent modulo
-- the corresponding stack permutation.
--
-- This file probes the proof.  The `refl` and `prep` cases are proven in
-- Agda below.  The `swap` case is analysed structurally (in prose); a
-- concrete counter-example shows the lemma is FALSE as stated — see the
-- analysis section.  The corrected lemma (under a "topologically
-- successful" precondition) is sketched but not implemented.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.EdgeReorder (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

module _ (H : Hypergraph FlatGen) where
  private
    module H = Hypergraph H

  private
    perm-of : ∀ {xs ys : List (Fin H.nV)} → xs Perm.↭ ys
            → HomTerm (unflatten (map H.vlab xs)) (unflatten (map H.vlab ys))
    perm-of p = permute-via-vlab H.vlab p

  ------------------------------------------------------------------------
  -- Goal statement: parameterised over `es₁ ↭ es₂` and an initial stack.
  ------------------------------------------------------------------------

  Goal : ∀ (es₁ es₂ : List (Fin H.nE)) → es₁ Perm.↭ es₂
       → List (Fin H.nV) → Set
  Goal es₁ es₂ _ s =
    Σ[ p ∈ proj₁ (process-edges H es₂ s) Perm.↭ proj₁ (process-edges H es₁ s) ]
       proj₂ (process-edges H es₁ s)
       ≈Term perm-of p ∘ proj₂ (process-edges H es₂ s)

  ------------------------------------------------------------------------
  -- Case 1: `refl`.  Both edge sequences are identical; the stacks and
  -- morphisms agree definitionally.  Bridging permutation is `refl`,
  -- which gives `id`; the equation reduces to `t ≈Term id ∘ t` via `idˡ`.
  ------------------------------------------------------------------------

  process-edges-↭-refl
    : ∀ (es : List (Fin H.nE)) (s : List (Fin H.nV))
    → Goal es es Perm.refl s
  process-edges-↭-refl es s = Perm.refl , FM.Equiv.sym FM.identityˡ

  ------------------------------------------------------------------------
  -- Case 2: `prep`.  Two sequences with a common head.  After firing
  -- the shared head, the remaining sequences are related by the IH.
  -- The bridging permutation is the IH's; morphism chain composes via
  -- associativity.
  ------------------------------------------------------------------------

  process-edges-↭-prep
    : ∀ (e : Fin H.nE) (es₁ es₂ : List (Fin H.nE))
        (es-↭ : es₁ Perm.↭ es₂)
        (ih : ∀ s' → Goal es₁ es₂ es-↭ s')
        (s : List (Fin H.nV))
    → Goal (e ∷ es₁) (e ∷ es₂) (Perm.prep e es-↭) s
  process-edges-↭-prep e es₁ es₂ es-↭ ih s
      with edge-step H s e
  ... | s' , t-head
      with ih s'
  ... | p-tail , eq-tail = p-tail , goal-eq
    where
      t-lhs = proj₂ (process-edges H es₁ s')
      t-rhs = proj₂ (process-edges H es₂ s')

      goal-eq : t-lhs ∘ t-head ≈Term perm-of p-tail ∘ (t-rhs ∘ t-head)
      goal-eq = begin
        t-lhs ∘ t-head             ≈⟨ eq-tail ⟩∘⟨refl ⟩
        (perm-of p-tail ∘ t-rhs) ∘ t-head ≈⟨ FM.assoc ⟩
        perm-of p-tail ∘ (t-rhs ∘ t-head) ∎

  ------------------------------------------------------------------------
  -- Case 3: `swap`.  THE VIABILITY TEST — and the architectural finding.
  --
  -- The natural statement of `swap` is FALSE in general.  Concrete
  -- counter-example: take H with two edges
  --
  --   e₁ : ein = [v₁], eout = [v₂]
  --   e₂ : ein = [v₂], eout = [v₃]
  --
  -- (e₂ depends on e₁'s output).  Starting from s = [v₁]:
  --
  --   process-edges H (e₁ ∷ e₂ ∷ []) [v₁]
  --     edge-step [v₁] e₁: fires, stack → [v₂].
  --     edge-step [v₂] e₂: fires, stack → [v₃].
  --     Final: ([v₃], _).
  --
  --   process-edges H (e₂ ∷ e₁ ∷ []) [v₁]
  --     edge-step [v₁] e₂: extract-prefix [v₂] [v₁] = nothing; SKIPS.
  --     edge-step [v₁] e₁: fires, stack → [v₂].
  --     Final: ([v₂], _).
  --
  -- Final stacks [v₃] vs [v₂] are NOT ↭-related.  The lemma as stated
  -- cannot be proven.
  --
  -- WHY this matters: the decoder's edge-step uses `extract-prefix`, which
  -- fails silently when a prerequisite vertex is missing.  Reordering
  -- edges past a dependency relation produces a different final state.
  -- For TOPOLOGICALLY VALID orderings (where every edge fires in its
  -- turn), both orderings produce the same final multiset.  For
  -- arbitrary `↭`, they don't.
  --
  -- THE CORRECT LEMMA: requires both orderings to be topologically
  -- successful.  Concretely:
  --
  --   AllFire : List (Fin H.nE) → List (Fin H.nV) → Set
  --   AllFire []       s = ⊤
  --   AllFire (e ∷ es) s = ∃[ rest ] ∃[ p ] extract-prefix (H.ein e) s
  --                                          ≡ just (rest, p)
  --                       × AllFire es (H.eout e ++ rest)
  --
  --   process-edges-↭-topo
  --     : ∀ (es₁ es₂ : List (Fin H.nE)) → es₁ ↭ es₂
  --     → ∀ (s : List (Fin H.nV))
  --     → AllFire es₁ s → AllFire es₂ s
  --     → Goal es₁ es₂ ? s    -- ? = trivial AllFire-derived perm
  --
  -- For Route 1's application (`H ≅ᴴ K` from `⟪f⟫ ≅ᴴ ⟪g⟫`), both H
  -- and K are translated and Linear; both `range nE_H` and `ψ⁻¹ ∘
  -- range nE_K` (the lifted natural-order on K) are topologically
  -- valid on H.  So `AllFire` holds for both — but proving this
  -- requires showing topological validity is preserved by the iso.
  --
  -- THE GOOD NEWS — σ-naturality on Agen edges is NOT required.
  --
  -- For the "both fire and don't interact" sub-case of swap (the most
  -- relevant for the σ-counter-example test), the proof obligation is:
  --
  --   mid'-e₂ ∘ perm₂ ∘ mid'-e₁ ∘ perm₁
  --     ≈Term stack-swap ∘ mid'-e₁' ∘ perm₁' ∘ mid'-e₂' ∘ perm₂'
  --
  -- where each `mid'-e` has the shape
  --   `unflatten-++-≅-to ∘ (Agen-edge e ⊗₁ id) ∘ unflatten-++-≅-from`.
  --
  -- The bridging chain decomposes through:
  --   (a) Mac Lane coherence (via `solveM`) to align the
  --       unflatten-++-≅ wrappers across the two rest-list shapes.
  --   (b) `⊗-∘-dist` to commute `(Agen e₁ ⊗ id)` and `(Agen e₂ ⊗ id)`
  --       past each other when their "rest" components are aligned.
  --   (c) Stack-permutation morphisms (`permute-via-vlab`) absorbed by
  --       `idˡ`/`idʳ`/structural σ on Fin-bijection permutations.
  --
  -- NONE of these steps need σ-naturality on the Agen edges themselves.
  -- The σ in the term tree appears only in (c), at the structural
  -- vertex-permutation layer — which is exactly where the existing
  -- `permute` infrastructure already absorbs it.
  --
  -- This is the KEY positive finding: the architectural blocker
  -- (σ-naturality between Agen edges) does NOT recur in Route 1.
  -- The "decoder places Agen edges side-by-side in tensor" structure
  -- means commutation is via `⊗-∘-dist`, not σ-naturality.
  --
  -- THE BAD NEWS — substantial Mac Lane chase per swap atom.
  --
  -- Each swap atom in `↭` requires its own ~50-100 LOC of Mac Lane
  -- chase to align the coherence wrappers across the two `rest`-list
  -- shapes.  For a long permutation (composed via `trans`), the chase
  -- compounds.  Plus the `AllFire` precondition and its preservation
  -- under iso adds substantial bookkeeping.
  --
  -- REVISED LOC ESTIMATE FOR ROUTE 1: ~1100-1550 LOC, up from initial
  -- 700.  Down to ~800-1000 if `solveM` extension absorbs the Mac
  -- Lane chase wholesale.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Case 4: `trans`.  Composition of IHs via `Perm.trans` and the
  -- corresponding morphism composition.  No architectural risk.  Not
  -- implemented here — depends on `swap` case structure.
  ------------------------------------------------------------------------
