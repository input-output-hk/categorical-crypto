{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The cospan-form decode algorithm.  For a hypergraph `H`, attempt to
-- build a `HomTerm (unflatten As) (unflatten Bs)`:
--
--   1. Start with stack `s = H.dom`.
--   2. For each edge `e` (in natural Fin order): if `H.ein e` is a
--      sub-multiset prefix of the stack, permute + apply the edge
--      generator + prepend `H.eout e`; otherwise skip (identity).
--   3. Finally extract `H.cod` as a full sub-multiset of the final stack
--      (empty residual ⇒ apply the permutation; else `nothing`).
--
-- The `nothing` case captures non-linear inputs and non-topologically-
-- sound edge orders.  For `⟪ f ⟫` the natural Fin order is sound, so
-- `decode-attempt ⟪ f ⟫` always returns `just _`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Decode (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
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
-- Multiset search (hypergraph-independent).  `extract-elem`/`extract-prefix`
-- are re-exported from a generic module so APROP and SMC versions are
-- definitionally equal.

open import Categories.Hypergraph.ExtractPrefix public
  using (extract-elem; extract-prefix)

-- `xs ++ [] ↭ xs`, at module scope for downstream `extract-exact` reasoning.
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
-- Apply an edge: recover the generator `g : mor A B` from `FlatGen.flat`,
-- then wrap with the unflatten-flatten coherence iso on each side.
-- Top-level (not under the `H` module) so downstream files can
-- `cong`-rewrite `Agen-edge` along `elab` equations without an `H` arg.
Agen-edge-aux
  : ∀ {ins outs : List X} → FlatGen ins outs
  → HomTerm (unflatten ins) (unflatten outs)
Agen-edge-aux (FlatGen.flat {A} {B} g) =
  _≅_.from (unflatten-flatten-≈ B) ∘ Agen g ∘ _≅_.to (unflatten-flatten-≈ A)

--------------------------------------------------------------------------------
-- The cospan algorithm, with `H` fixed.

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

  Agen-edge
    : (e : Fin H.nE)
    → HomTerm (unflatten (map H.vlab (H.ein e)))
              (unflatten (map H.vlab (H.eout e)))
  Agen-edge e = Agen-edge-aux (H.elab e)

  --------------------------------------------------------------------
  -- Per-edge step.  On finding `H.ein e` in the stack: permute it to the
  -- front, apply the edge generator (identity on the residual), update the
  -- stack to `H.eout e ++ rest`.  On failure: identity.

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

      -- Bridge `map vlab (xs ++ ys) ≡ map vlab xs ++ map vlab ys` (`map-++`).
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
  -- Process all edges in natural Fin order; returns the final stack and
  -- a HomTerm from the original stack.

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
  -- Run the algorithm from `H.dom`, then bridge the final stack to
  -- `H.cod` via a final permute.

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
