{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5f Step 3 — Constructive `decode` (cospan-form algorithm).
--
-- Given a hypergraph `H : Hypergraph FlatGen As Bs`, we attempt to build a
-- `HomTerm (unflatten As) (unflatten Bs)` using the cospan-form algorithm:
--
--   1. Initial stack `s = H.dom`.
--   2. For each edge `e : Fin H.nE` (in natural Fin order):
--      a. Search for `H.ein e` as a sub-multiset prefix of the current stack.
--      b. If found: permute, apply the edge generator, prepend `H.eout e`.
--      c. If not: skip (apply identity).
--   3. Final search: extract `H.cod` as a (full) sub-multiset of the final
--      stack.  If found with empty residual: apply the resulting permutation.
--      Otherwise: return `nothing`.
--
-- The algorithm returns `Maybe (HomTerm (unflatten As) (unflatten Bs))` —
-- the `nothing` case captures non-linear inputs (where the multisets
-- don't match) and linear-but-non-topologically-sound edge orders.
-- For hypergraphs translated from `⟪ f ⟫`, the natural Fin order *is*
-- topologically sound (by the smart constructors of `FromAPROP`), so
-- `decode-attempt ⟪ f ⟫` always returns `just _`.
--
-- The downstream `decode` postulate in `Decoder.agda` is still in place;
-- the eventual goal is to replace it with `from-just (decode-attempt H)`
-- guarded by a (postponed) totality lemma `decode-attempt-Linear`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Decode (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; subst₂)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Multiset search.  These are independent of the hypergraph and live
-- at top-level so foundation lemmas (`DecodeProperties.agda`) can talk
-- about them without H-parametrisation.

-- `extract-elem` and `extract-prefix` are re-exported from a generic
-- module so that downstream bridges (e.g.
-- `Categories.APROP.Hypergraph.Completeness.Discharge.APROPMacLaneFromSMC`)
-- observe definitional equality between APROP and SMC versions.
open import Categories.Hypergraph.ExtractPrefix public
  using (extract-elem; extract-prefix)

-- `xs ++ [] ↭ xs`.  Lifted to module scope (was previously local to
-- `extract-exact`'s where-clause) so downstream lemmas can refer to it
-- when reasoning about `extract-exact`'s perm output.
++-[]-↭ : ∀ {n} (l : List (Fin n)) → l ++ [] Perm.↭ l
++-[]-↭ []       = Perm.refl
++-[]-↭ (x ∷ xs) = Perm.prep x (++-[]-↭ xs)

-- Specialised search for an exact multiset match: look for `ks`
-- with empty residual.  Used at the final step to bridge to `H.cod`.
extract-exact
  : ∀ {n} (ks xs : List (Fin n))
  → Maybe (xs Perm.↭ ks)
extract-exact ks xs with extract-prefix ks xs
... | nothing       = nothing
... | just ([]    , p) = just (Perm.trans p (++-[]-↭ ks))
... | just (_ ∷ _ , _) = nothing

--------------------------------------------------------------------------------
-- Apply an edge: pattern-match `H.elab e` to recover the underlying
-- generator `g : mor A B`, then wrap with the unflatten-flatten
-- coherence iso on each side.

-- Auxiliary helper: pattern-match `FlatGen.flat` indirectly through
-- explicit propositional equalities.  The naive `with H.elab e | flat
-- g` doesn't work because Agda can't unify `flatten A` with the
-- generic `map H.vlab (H.ein e)`.
--
-- Top-level (not nested inside the `module _ (H : Hypergraph FlatGen)`
-- below) so downstream files can `cong`-rewrite under it when
-- transporting `Agen-edge` along `elab` equations — no `H` argument is
-- needed.
Agen-edge-aux
  : ∀ {ins outs : List X} → FlatGen ins outs
  → HomTerm (unflatten ins) (unflatten outs)
Agen-edge-aux (FlatGen.flat {A} {B} g) =
  _≅_.from (unflatten-flatten-≈ B) ∘ Agen g ∘ _≅_.to (unflatten-flatten-≈ A)

--------------------------------------------------------------------------------
-- Open H once at the module level for the cospan algorithm.

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

  Agen-edge
    : (e : Fin H.nE)
    → HomTerm (unflatten (map H.vlab (H.ein e)))
              (unflatten (map H.vlab (H.eout e)))
  Agen-edge e = Agen-edge-aux (H.elab e)

  --------------------------------------------------------------------
  -- Per-edge step.  Search the stack for `H.ein e`; on success, permute
  -- to bring `H.ein e` to the front, apply the edge generator (with
  -- identity on the residual), then update the stack to
  -- `H.eout e ++ rest`.  On failure, fall back to identity.

  edge-step
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  edge-step s e with extract-prefix (H.ein e) s
  ... | nothing             = (s , id)
  ... | just (rest , perm)  = (H.eout e ++ rest , bridged)
    where
      ein-l  = map H.vlab (H.ein e)
      eout-l = map H.vlab (H.eout e)
      rest-l = map H.vlab rest

      -- Apply the edge generator at the front, identity on the rest.
      mid : HomTerm (unflatten (ein-l  ++ rest-l))
                    (unflatten (eout-l ++ rest-l))
      mid = _≅_.to   (unflatten-++-≅ eout-l rest-l)
            ∘ (Agen-edge e ⊗₁ id)
            ∘ _≅_.from (unflatten-++-≅ ein-l  rest-l)

      -- Bridge `map vlab (xs ++ ys) ≡ map vlab xs ++ map vlab ys`
      -- (definitionally not, but propositionally via `map-++`).
      mid' : HomTerm (unflatten (map H.vlab (H.ein e  ++ rest)))
                     (unflatten (map H.vlab (H.eout e ++ rest)))
      mid' = subst₂ HomTerm
              (cong unflatten (sym (map-++ H.vlab (H.ein  e) rest)))
              (cong unflatten (sym (map-++ H.vlab (H.eout e) rest)))
              mid

      bridged : HomTerm (unflatten (map H.vlab s))
                        (unflatten (map H.vlab (H.eout e ++ rest)))
      bridged = mid' ∘ permute-via-vlab H.vlab perm

  --------------------------------------------------------------------
  -- Process all edges in natural Fin order.  Returns the final stack
  -- and a HomTerm from the original stack.

  process-edges
    : List (Fin H.nE) → ∀ (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  process-edges []       s = (s , id)
  process-edges (e ∷ es) s =
    let (s'  , t)  = edge-step    s  e
        (s'' , t') = process-edges es s'
    in  (s'' , t' ∘ t)

  process-all-edges
    : ∀ (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  process-all-edges = process-edges (range H.nE)

  --------------------------------------------------------------------
  -- Top-level.  Run the cospan-form algorithm starting from `H.dom`,
  -- then attempt to bridge the final stack to `H.cod` via a final
  -- permute.

  -- With the de-indexed Hypergraph, `decode-attempt` returns at the
  -- *computed* boundary type (`unflatten (domL H)` to `unflatten (codL H)`)
  -- — no `subst₂ HomTerm` boundary wrap is needed, because there's no
  -- index-level boundary equation to bridge across.
  decode-attempt
    : Maybe (HomTerm (unflatten (domL H)) (unflatten (codL H)))
  decode-attempt with process-all-edges H.dom
  ... | (s_final , process-term) with extract-exact H.cod s_final
  ...    | nothing   = nothing
  ...    | just perm = just (final-permute ∘ process-term)
    where
      final-permute : HomTerm (unflatten (map H.vlab s_final))
                              (unflatten (map H.vlab H.cod))
      final-permute = permute-via-vlab H.vlab perm
